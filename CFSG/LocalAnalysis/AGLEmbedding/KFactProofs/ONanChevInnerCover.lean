module

public import CFSG.Open.GLBDefs
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover

@[expose] def LiftsComm {L : Type*} [Group L] (E : Subgroup L) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* L), Function.Surjective φ →
    φ.ker ≤ Subgroup.center Y → ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x

theorem LiftsComm.map_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    {E : Subgroup L} (h : LiftsComm E) : LiftsComm (E.map e.toMonoidHom) := by
  intro Y _ _ φ hφ hker x hx y hy
  have key : ∀ z ∈ (E.map e.toMonoidHom).comap φ, z ∈ E.comap (e.symm.toMonoidHom.comp φ) := by
    intro z hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hz)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← haz]
    simpa using ha
  refine h Y (e.symm.toMonoidHom.comp φ) (e.symm.surjective.comp hφ) (fun z hz => hker ?_) x
    (key x hx) y (key y hy)
  simpa using hz

theorem liftsComm_of_inverters {L : Type*} [Group L] {ι : Type} [Fintype ι] [DecidableEq ι]
    (h w : ι → L) (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) :
    IsElemAbelian 3 (Subgroup.closure (Set.range h)) ∧
      Nat.card (Subgroup.closure (Set.range h)) = 3 ^ Fintype.card ι ∧
      LiftsComm (Subgroup.closure (Set.range h)) := by
  have hid := inversion_basis_package (φ := MonoidHom.id L) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) Nat.prime_three (by norm_num) h w hcomm hord hinv hfix
  exact ⟨hid.1, hid.2.1, fun Y _ _ φ hφ hker =>
    (inversion_basis_package hφ hker Nat.prime_three (by norm_num) h w hcomm hord hinv hfix).2.2⟩

theorem liftsComm_of_swaps {L : Type*} [Group L]
    (θ : Multiplicative (Fin 4 → ZMod 3) →* L) (hθ : Function.Injective θ)
    (g : Fin 4 → Fin 4 → L)
    (hg₁ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single i 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single j 1)))
    (hg₂ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single j 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single i 1))) :
    (∀ x ∈ θ.range, x ^ 3 = 1) ∧ Nat.card θ.range = 3 ^ 4 ∧ LiftsComm θ.range := by
  have hcommθ : ∀ x y : Multiplicative (Fin 4 → ZMod 3), Commute (θ x) (θ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hpow : ∀ x : Multiplicative (Fin 4 → ZMod 3), θ x ^ 3 = 1 := fun x => by
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      have h3 : (3 : ZMod 3) = 0 := by decide
      simp [h3]
    rw [this, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hpow x
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, Nat.card_congr Multiplicative.toAdd]
    simp
  · intro Y _ _ φ hφ hker x hx y hy
    have hone : ∀ a a' : Multiplicative (Fin 4 → ZMod 3), liftComm φ hφ (θ a) (θ a') = 1 := by
      refine liftComm_eq_one_of_closure hφ hker θ
        (S := Set.range fun j : Fin 4 => Pi.single j (1 : ZMod 3)) closure_range_single_eq_top ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      by_cases hij : i = j
      · subst hij
        exact liftComm_self hφ _
      · exact liftComm_eq_one_of_conj_swap hφ hker (p := 3) (by decide) (hcommθ _ _) (hpow _)
          (g i j) (hg₁ i j hij) (hg₂ i j hij)
    exact mul_comm_of_liftComm_eq_one hφ hker (U := θ.range)
      (fun s hs t ht => by
        obtain ⟨a, rfl⟩ := hs
        obtain ⟨b, rfl⟩ := ht
        exact hone a b) hx hy

@[expose] def LiftableNormalizerGen (L : Type*) [Group L] : Prop :=
  ∃ (E : Subgroup L) (S : Set (Subgroup L)), (∀ x ∈ E, x ^ 3 = 1) ∧ 3 ^ 3 ≤ Nat.card E ∧
    S.Nonempty ∧ (∀ F ∈ S, F ≤ E ∧ 3 ^ 2 ≤ Nat.card F) ∧ LiftsComm E ∧
    ⊤ ≤ ⨆ F ∈ S, Subgroup.normalizer (F : Set L)

theorem weakCore_top_of_cover {K L : Type} [Group K] [Finite K] [Group L] (π : K →* L)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {E : Subgroup L} {S : Set (Subgroup L)} (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hE : 3 ^ 3 ≤ Nat.card E) (hSne : S.Nonempty) (hS : ∀ F ∈ S, F ≤ E ∧ 3 ^ 2 ≤ Nat.card F)
    (hcomm : ∀ x ∈ E.comap π, ∀ y ∈ E.comap π, x * y = y * x)
    (hgen : ⊤ ≤ ⨆ F ∈ S, Subgroup.normalizer (F : Set L)) {T : Subgroup K}
    (hT : E.comap π ≤ T) : GLBWeakCore 3 T = ⊤ := by
  have hp : 1 < 3 := by norm_num
  obtain ⟨V, hVE, hVab, hVcard, -⟩ := exists_elemAbelian_le_centralizer (φ := π) hπ hker
    Nat.prime_three (by norm_num) hE3 hcomm hE (u := 1) (by simp)
    (fun x _ => by rw [map_one]; exact Commute.one_left _)
  have hN : ∀ F ∈ S, Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) ≤
      GLBWeakCore 3 T := by
    intro F hF
    have hFE : F.comap π ≤ E.comap π := Subgroup.comap_mono (hS F hF).1
    refine le_sSup ⟨F.comap π, hFE.trans hT, ?_, ?_, rfl⟩
    · obtain ⟨W, hW, hWab, hWcard, -⟩ := exists_elemAbelian_le_centralizer (φ := π) hπ hker
        Nat.prime_three (by norm_num) (fun x hx => hE3 x ((hS F hF).1 hx))
        (fun x hx y hy => hcomm x (hFE hx) y (hFE hy)) (hS F hF).2 (u := 1) (by simp)
        (fun x _ => by rw [map_one]; exact Commute.one_left _)
      exact SectionRank.le_pRank hp hW hWab hWcard
    · refine SectionRank.le_pRank hp (E := V) ?_ hVab hVcard
      refine le_sup_of_le_right (le_inf (hVE.trans hT) ?_)
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact hcomm q (hFE hq) v (hVE hv)
  set M : Subgroup K := ⨆ F ∈ S, Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) with hM
  have hMle : M ≤ GLBWeakCore 3 T := iSup₂_le fun F hF => hN F hF
  have himg : M.map π = ⊤ := by
    rw [eq_top_iff]
    refine hgen.trans (iSup₂_le fun F hF l hl => ?_)
    obtain ⟨x, rfl⟩ := hπ l
    refine Subgroup.mem_map.2 ⟨x, ?_, rfl⟩
    have hrange : F ≤ π.range := by
      rw [MonoidHom.range_eq_top.2 hπ]
      exact le_top
    have hx : x ∈ Subgroup.normalizer ((F.comap π : Subgroup K) : Set K) := by
      rw [← Subgroup.comap_normalizer_eq_of_le_range hrange]
      exact hl
    exact (le_iSup₂ (f := fun F (_ : F ∈ S) =>
      Subgroup.normalizer ((F.comap π : Subgroup K) : Set K)) F hF) hx
  obtain ⟨F₀, hF₀⟩ := hSne
  have hkerM : π.ker ≤ M := fun z hz =>
    (le_iSup₂ (f := fun F (_ : F ∈ S) => Subgroup.normalizer ((F.comap π : Subgroup K) : Set K))
      F₀ hF₀) (Subgroup.center_le_normalizer _ (hker hz))
  refine eq_top_iff.2 fun x _ => hMle ?_
  have hmem : π x ∈ M.map π := by
    rw [himg]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hmem
  have hker' : m⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  have : x = m * (m⁻¹ * x) := by group
  rw [this]
  exact M.mul_mem hm (hkerM hker')

theorem LiftableNormalizerGen.of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : LiftableNormalizerGen L) : LiftableNormalizerGen L' := by
  obtain ⟨E, S, hE3, hE, hSne, hS, hlift, hgen⟩ := h
  have hcard : ∀ F : Subgroup L, Nat.card (F.map e.toMonoidHom) = Nat.card F := fun F =>
    Subgroup.card_map_of_injective e.injective
  refine ⟨E.map e.toMonoidHom, (fun F => F.map e.toMonoidHom) '' S, ?_, ?_, hSne.image _, ?_,
    hlift.map_mulEquiv e, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE3 x hx, map_one]
  · rw [hcard]
    exact hE
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨Subgroup.map_mono (hS F hF).1, by rw [hcard]; exact (hS F hF).2⟩
  · have hle : (⨆ F ∈ S, Subgroup.normalizer (F : Set L)) ≤
        (⨆ F' ∈ (fun F : Subgroup L => F.map e.toMonoidHom) '' S,
          Subgroup.normalizer (F' : Set L')).comap e.toMonoidHom := by
      refine iSup₂_le fun F hF z hz => ?_
      have h1 : e.toMonoidHom z ∈ Subgroup.normalizer ((F.map e.toMonoidHom : Subgroup L') :
          Set L') := Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hz)
      exact (le_iSup₂ (f := fun F' (_ : F' ∈ (fun F : Subgroup L => F.map e.toMonoidHom) '' S) =>
        Subgroup.normalizer (F' : Set L')) (F.map e.toMonoidHom) ⟨F, hF, rfl⟩) h1
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    exact hle (hgen (Subgroup.mem_top x))

theorem weakCore_eq_top_of_normalizerGen {K L : Type} [Group K] [Finite K] [Group L]
    (hL : LiftableNormalizerGen L) (e : K ⧸ Subgroup.center K ≃* L)
    (hZ : IsPGroup 3 (Subgroup.center K)) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨E, S, hE3, hE, hSne, hS, hlift, hgen⟩ := hL
  set π : K →* L := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hπdef
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  have hP : IsPGroup 3 (E.comap π) := hEp.comap_of_ker_isPGroup π (hker ▸ hZ)
  obtain ⟨T₀, hT₀⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  have hTmap : (T : Subgroup K) = (T₀ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set π' : K →* L := π.comp (MulAut.conj g⁻¹).toMonoidHom with hπ'def
  have hπ' : Function.Surjective π' := hπ.comp (MulAut.conj g⁻¹).surjective
  have hπ'x : ∀ x, π' x = π (g⁻¹ * x * g) := fun x => by
    simp [hπ'def]
  have hker' : π'.ker ≤ Subgroup.center K := by
    intro x hx
    have h1 : g⁻¹ * x * g ∈ Subgroup.center K := by
      rw [← hker, MonoidHom.mem_ker, ← hπ'x]
      exact hx
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [← h2]
    exact (inferInstance : (Subgroup.center K).Normal).conj_mem _ h1 g
  refine weakCore_top_of_cover π' hπ' hker' hE3 hE hSne hS (hlift K π' hπ' hker') hgen ?_
  intro x hx
  have hx' : g⁻¹ * x * g ∈ E.comap π := by
    rw [Subgroup.mem_comap, ← hπ'x]
    exact hx
  rw [hTmap]
  exact ⟨g⁻¹ * x * g, hT₀ hx', by simp [mul_assoc]⟩

section Inverters

theorem mem_normalizer_of_forall_commute {G : Type*} [Group G] (H : Subgroup G) {x : G}
    (h : ∀ y ∈ H, Commute x y) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [(h y hy).mul_inv_cancel]
    exact hy
  · intro hy
    have hc := (h _ hy).eq
    have hxy : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹)) := by group
        _ = x⁻¹ * (x * y * x⁻¹ * x) := by rw [hc]
        _ = y := by group
    rwa [hxy] at hy

theorem mem_normalizer_closure_of_commute {G : Type*} [Group G] {s : Set G} {x : G}
    (h : ∀ y ∈ s, Commute x y) : x ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  have hle : Subgroup.closure s ≤ Subgroup.centralizer {x} :=
    (Subgroup.closure_le _).2 fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.2 (h t ht).symm.eq
  refine mem_normalizer_of_forall_commute _ fun y hy => ?_
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem mem_normalizer_closure_of_conj_mem_inv {G : Type*} [Group G] {s : Set G} {g : G}
    (h1 : ∀ t ∈ s, g * t * g⁻¹ ∈ Subgroup.closure s)
    (h2 : ∀ t ∈ s, g⁻¹ * t * g ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  have hmap : ∀ u : G, (∀ t ∈ s, u * t * u⁻¹ ∈ Subgroup.closure s) →
      ∀ y ∈ Subgroup.closure s, u * y * u⁻¹ ∈ Subgroup.closure s := by
    intro u hu y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact hu t ht
    | one => simp
    | mul a b _ _ ha hb =>
      have : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
      rw [this]
      exact mul_mem ha hb
    | inv a _ ha =>
      have : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hmap g h1 y, fun hy => ?_⟩
  have := hmap g⁻¹ (fun t ht => by simpa using h2 t ht) _ hy
  simpa [mul_assoc] using this

@[expose] def pairSubgroup {L : Type*} [Group L] (h : Fin 4 → L) (j k : Fin 4) : Subgroup L :=
  Subgroup.closure (Set.range ![h j, h k])

@[expose] def pairCentralizing {L : Type*} [Group L] (h : Fin 4 → L) : Set L :=
  {x | ∃ j k, j ≠ k ∧ Commute x (h j) ∧ Commute x (h k)}

theorem liftableNormalizerGen_of_inverters {L : Type*} [Group L] (h w : Fin 4 → L)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j)
    (hgen : Subgroup.closure (pairCentralizing h ∪
      (Subgroup.normalizer (Subgroup.closure (Set.range h) : Set L) : Set L)) = ⊤) :
    LiftableNormalizerGen L := by
  obtain ⟨hEab, hEcard, hElift⟩ := liftsComm_of_inverters h w hcomm hord hinv hfix
  have hpair : ∀ j k : Fin 4, j ≠ k → Nat.card (pairSubgroup h j k) = 3 ^ 2 := by
    intro j k hjk
    have := (liftsComm_of_inverters (L := L) (ι := Fin 2) ![h j, h k] ![w j, w k]
      (fun a b => by fin_cases a <;> fin_cases b <;> exact hcomm _ _)
      (fun a => by fin_cases a <;> exact hord _)
      (fun a => by fin_cases a <;> exact hinv _)
      (fun a b hab => by
        fin_cases a <;> fin_cases b
        · exact absurd rfl hab
        · exact hfix j k hjk
        · exact hfix k j hjk.symm
        · exact absurd rfl hab)).2.1
    simpa [pairSubgroup] using this
  have hpairle : ∀ j k : Fin 4, pairSubgroup h j k ≤ Subgroup.closure (Set.range h) := by
    intro j k
    refine Subgroup.closure_mono ?_
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · exact ⟨j, rfl⟩
    · exact ⟨k, rfl⟩
  refine ⟨Subgroup.closure (Set.range h),
    {F | (∃ j k, j ≠ k ∧ F = pairSubgroup h j k) ∨ F = Subgroup.closure (Set.range h)},
    hEab.2, ?_, ⟨_, Or.inr rfl⟩, ?_, hElift, ?_⟩
  · rw [hEcard]
    simp
  · rintro F (⟨j, k, hjk, rfl⟩ | rfl)
    · exact ⟨hpairle j k, (hpair j k hjk).ge⟩
    · refine ⟨le_rfl, ?_⟩
      rw [hEcard]
      simp
  · rw [← hgen, Subgroup.closure_le]
    rintro x (⟨j, k, hjk, hxj, hxk⟩ | hx)
    · have hxn : x ∈ Subgroup.normalizer (pairSubgroup h j k : Set L) :=
        mem_normalizer_closure_of_commute fun y hy => by
          rcases hy with ⟨a, rfl⟩
          fin_cases a
          · exact hxj
          · exact hxk
      exact (le_iSup₂ (f := fun F (_ : F ∈ {F | (∃ j k, j ≠ k ∧ F = pairSubgroup h j k) ∨
        F = Subgroup.closure (Set.range h)}) => Subgroup.normalizer (F : Set L))
        (pairSubgroup h j k) (Or.inl ⟨j, k, hjk, rfl⟩)) hxn
    · exact (le_iSup₂ (f := fun F (_ : F ∈ {F | (∃ j k, j ≠ k ∧ F = pairSubgroup h j k) ∨
        F = Subgroup.closure (Set.range h)}) => Subgroup.normalizer (F : Set L))
        (Subgroup.closure (Set.range h)) (Or.inr rfl)) hx

end Inverters

end CFSG.AGLEmbedding
