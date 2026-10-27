module

public import CFSG.CGT.PushingUpLit.BHS.FourSixB
public import CFSG.CGT.PushingUpLit.BHS.FourSymD
public import CFSG.CGT.PushingUpLit.BHS.FourSymC
public import CFSG.CGT.PushingUpLit.BHSSym.Coxeter
public import CFSG.CGT.PushingUpLit.BHSSym.Delta
public import CFSG.CGT.PushingUpLit.BHSSym.Stabilizer

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.RankThree.PartOne
  CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

variable {V : Type} [CommGroup V] [Finite V]

structure SymCore (D : Set (Subgroup (MulAut V))) (E : Subgroup (MulAut V)) (m : ℕ) where
  θ : ↥E ≃* Equiv.Perm (Fin m)
  β : ↥(commV E) →* coreMod m
  odd : Odd m
  three_le : 3 ≤ m
  inv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E
  surj : Function.Surjective β
  ker : β.ker = ⊥
  equiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
    β ⟨(x : MulAut V) p, hp⟩ = coreAct m (θ x) (β p)
  top : commV E ⊔ fixV E = ⊤
  trans : ∀ B ∈ dInter D E, ∃ i j : Fin m, i ≠ j ∧ ∀ b : ↥E, (b : MulAut V) ∈ B →
    θ b = 1 ∨ θ b = Equiv.swap i j
  cls : ∀ i j : Fin m, i ≠ j → ∃ B ∈ dInter D E, ∀ b : ↥E, (b : MulAut V) ∈ B ↔
    θ b = 1 ∨ θ b = Equiv.swap i j

structure SymData (M : Subgroup (MulAut V)) (D : Set (Subgroup (MulAut V)))
    (E : Subgroup (MulAut V)) (m : ℕ) extends SymCore D E m where
  pt : ∃ i₀ : Fin m, ∀ x : ↥E, (x : MulAut V) ∈ M ↔ θ x i₀ = i₀

theorem symCore_of_chain {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1) (hconn : ConnD D) {k : ℕ} (hk : Even k)
    (hk2 : 2 ≤ k) (x : ℕ → MulAut V) (u : ℕ → V) (hx : ∀ i < k, IsTransv (x i) (u i))
    (hxD : ∀ i < k, Subgroup.zpowers (x i) ∈ D)
    (hadj : ∀ i, i + 1 < k → x i * x (i + 1) ≠ x (i + 1) * x i)
    (hfar : ∀ i j, i + 2 ≤ j → j < k → x i * x j = x j * x i)
    (hne : ∀ i < k, ∀ j < k, i ≠ j → x i ≠ x j)
    (hgen : Subgroup.closure (x '' Set.Iio k) = P) :
    ∃ d : SymCore D P (k + 1), ∀ i : ℕ, i < k → ∀ hP : x i ∈ P,
      d.θ ⟨x i, hP⟩ = adjSwap k i := by
  have hxP : ∀ i < k, x i ∈ P := fun i hi => by
    rw [← hgen]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hrel : ∀ i, i + 1 < k → x i (u (i + 1)) = u (i + 1) * u i ∧
      x (i + 1) (u i) = u i * u (i + 1) ∧ u i ≠ u (i + 1) := fun i hi =>
    Hyp41.rel_of_noncomm h hV (hxD i (by omega)) (hxD (i + 1) hi) (hx i (by omega))
      (hx (i + 1) hi) rfl rfl (hadj i hi)
  have hcox : IsCoxeterA k x :=
    { sq := fun i hi => (hx i hi).sq
      braid := fun i hi => IsTransv.braid hV (hx i (by omega)) (hx (i + 1) hi) (hrel i hi).1
        (hrel i hi).2.1
      comm := fun i j hij hj => hfar i j hij hj }
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_perm_of_isCoxeterA hk2 P x hcox hxP hne
    (fun i hi => (hx i hi).ne_one) hgen
  have hmfar : ∀ i j, i < k → j < k → j ≠ i + 1 → i ≠ j + 1 → x i (u j) = u j := by
    intro i j hi hj h1 h2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ((IsTransv.comm_iff hV (hx i hi) (hx j hj)).1 (hfar i j (by omega) hj)).1
    · subst hij
      exact (hx i hi).apply_centre hV
    · exact ((IsTransv.comm_iff hV (hx j hj) (hx i hi)).1 (hfar j i (by omega) hi)).2
  obtain ⟨β, hinv, hsurj, hker, hβgen, htop⟩ := exists_module_identification hV hk hk2 x u hx
    (fun i hi => ⟨(hrel i hi).1, (hrel i hi).2.1⟩) hmfar hgen
  have hequiv : ∀ (g : MulAut V) (hg : g ∈ Subgroup.closure (x '' Set.Iio k))
      (hgP : g ∈ P) (p : ↥(commV P)) (hp : g p ∈ commV P),
      β ⟨g p, hp⟩ = coreAct (k + 1) (θ ⟨g, hgP⟩) (β p) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g' hg' =>
      obtain ⟨i, hi, rfl⟩ := hg'
      intro hgP p hp
      have hi' : i < k := hi
      rw [hθ i hi']
      exact hβgen i hi' p hp
    | one =>
      intro hgP p hp
      have : θ ⟨1, hgP⟩ = 1 := map_one θ
      rw [this, map_one]
      rfl
    | mul a b ha hb iha ihb =>
      intro hgP p hp
      have haP : a ∈ P := hgen ▸ ha
      have hbP : b ∈ P := hgen ▸ hb
      have hbp : b p ∈ commV P := hinv b hbP p p.2
      have e3 : θ ⟨a * b, hgP⟩ = θ ⟨a, haP⟩ * θ ⟨b, hbP⟩ := by
        rw [← map_mul]
        rfl
      calc β ⟨(a * b) p, hp⟩ = β ⟨a (b p), by simpa using hp⟩ := rfl
        _ = coreAct (k + 1) (θ ⟨a, haP⟩) (β ⟨b p, hbp⟩) := iha haP ⟨b p, hbp⟩ _
        _ = coreAct (k + 1) (θ ⟨a, haP⟩) (coreAct (k + 1) (θ ⟨b, hbP⟩) (β p)) := by
          rw [ihb hbP p hbp]
        _ = coreAct (k + 1) (θ ⟨a * b, hgP⟩) (β p) := by
          rw [e3, MonoidHom.map_mul]
          rfl
    | inv a ha iha =>
      intro hgP p hp
      have haP : a ∈ P := hgen ▸ ha
      have e1 := iha haP ⟨a⁻¹ p, hp⟩ (by
        show a (a⁻¹ p) ∈ commV P
        simp)
      have e2 : θ ⟨a⁻¹, hgP⟩ = (θ ⟨a, haP⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      have key : coreAct (k + 1) (θ ⟨a, haP⟩) (β ⟨a⁻¹ p, hp⟩) = β p := by
        rw [← e1]
        congr 1
        exact Subtype.ext (by simp)
      have step1 : β ⟨a⁻¹ p, hp⟩ = coreAct (k + 1) (θ ⟨a, haP⟩)⁻¹ (β p) := by
        rw [← key, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [step1, e2, map_inv]
  have hequiv' : ∀ (g : ↥P) (p : ↥(commV P)) (hp : (g : MulAut V) p ∈ commV P),
      β ⟨(g : MulAut V) p, hp⟩ = coreAct (k + 1) (θ g) (β p) := fun g p hp =>
    hequiv g (hgen ▸ g.2) g.2 p hp
  have hx0D : Subgroup.zpowers (x 0) ∈ D := hxD 0 (by omega)
  obtain ⟨a₀, b₀, hab₀, hs0⟩ : ∃ a b : Fin (k + 1), a ≠ b ∧ adjSwap k 0 = Equiv.swap a b :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], adjSwap_of_lt (by omega)⟩
  have hθ0 : ∀ hP : x 0 ∈ P, θ ⟨x 0, hP⟩ = Equiv.swap a₀ b₀ := fun hP => by
    have := hθ 0 (by omega)
    rw [hs0] at this
    exact this
  have htrans : ∀ B ∈ dInter D P, ∃ i j : Fin (k + 1), i ≠ j ∧ ∀ b : ↥P, (b : MulAut V) ∈ B →
      θ b = 1 ∨ θ b = Equiv.swap i j := by
    intro B hB
    obtain ⟨g, hgP, hBg⟩ := h.exists_conj_of_connD hconn hx0D hB.1
    rw [conjSub_zpowers] at hBg
    have hy2 := (IsTransv.conj g (hx 0 (by omega))).sq
    refine ⟨θ ⟨g, hgP⟩ a₀, θ ⟨g, hgP⟩ b₀, fun e => hab₀ ((θ ⟨g, hgP⟩).injective e),
      fun b hb => ?_⟩
    rw [hBg] at hb
    rcases eq_one_or_of_mem_zpowers hy2 hb with h1 | h1
    · left
      have : b = 1 := Subtype.ext h1
      rw [this, map_one]
    · right
      have hb' : b = ⟨g, hgP⟩ * ⟨x 0, hxP 0 (by omega)⟩ * ⟨g, hgP⟩⁻¹ :=
        Subtype.ext (by rw [h1]; rfl)
      rw [hb', map_mul, map_mul, map_inv, hθ0 (hxP 0 (by omega))]
      exact (Equiv.swap_apply_apply (θ ⟨g, hgP⟩) a₀ b₀).symm
  have hcls : ∀ i j : Fin (k + 1), i ≠ j → ∃ B ∈ dInter D P, ∀ b : ↥P, (b : MulAut V) ∈ B ↔
      θ b = 1 ∨ θ b = Equiv.swap i j := by
    intro i j hij
    have hinj1 : Function.Injective (![a₀, b₀] : Fin 2 → Fin (k + 1)) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hinj2 : Function.Injective (![i, j] : Fin 2 → Fin (k + 1)) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hinj1 hinj2
    have hσa : σ a₀ = i := hσ 0
    have hσb : σ b₀ = j := hσ 1
    set g : ↥P := θ.symm σ with hg
    have hBD : conjSub (g : MulAut V) (Subgroup.zpowers (x 0)) ∈ D :=
      h.conj_mem _ hx0D _ g.2
    have hy2 := (IsTransv.conj (g : MulAut V) (hx 0 (by omega))).sq
    have hyP : (g : MulAut V) * x 0 * (g : MulAut V)⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem g.2 (hxP 0 (by omega))) (P.inv_mem g.2)
    have hθy : θ ⟨(g : MulAut V) * x 0 * (g : MulAut V)⁻¹, hyP⟩ = Equiv.swap i j := by
      have : (⟨(g : MulAut V) * x 0 * (g : MulAut V)⁻¹, hyP⟩ : ↥P) =
          g * ⟨x 0, hxP 0 (by omega)⟩ * g⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hθ0 (hxP 0 (by omega)), hg, MulEquiv.apply_symm_apply,
        ← hσa, ← hσb]
      exact (Equiv.swap_apply_apply σ a₀ b₀).symm
    refine ⟨conjSub (g : MulAut V) (Subgroup.zpowers (x 0)), ⟨hBD, h.le _ hBD⟩, fun b => ?_⟩
    rw [conjSub_zpowers]
    constructor
    · intro hb
      rcases eq_one_or_of_mem_zpowers hy2 hb with h1 | h1
      · left
        have : b = 1 := Subtype.ext h1
        rw [this, map_one]
      · right
        have : b = ⟨(g : MulAut V) * x 0 * (g : MulAut V)⁻¹, hyP⟩ := Subtype.ext h1
        rw [this, hθy]
    · rintro (h1 | h1)
      · have : b = 1 := θ.injective (by rw [h1, map_one])
        rw [this]
        exact Subgroup.one_mem _
      · have : b = ⟨(g : MulAut V) * x 0 * (g : MulAut V)⁻¹, hyP⟩ :=
          θ.injective (by rw [h1, hθy])
        rw [this]
        exact Subgroup.mem_zpowers _
  refine ⟨
    { θ := θ
      β := β
      odd := hk.add_one
      three_le := by omega
      inv := hinv
      surj := hsurj
      ker := hker
      equiv := hequiv'
      top := htop
      trans := htrans
      cls := hcls }, fun i hi hP => hθ i hi⟩

section Point

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)}
  {m : ℕ}

omit [Finite V] in
theorem SymCore.exists_swap_of_mem (d : SymCore D P m) {A : Subgroup (MulAut V)}
    (hA : A ∈ dInter D P) (hne : A ≠ ⊥) :
    ∃ i j : Fin m, i ≠ j ∧ ∀ b : ↥P, (b : MulAut V) ∈ A ↔ d.θ b = 1 ∨ d.θ b = Equiv.swap i j := by
  obtain ⟨i, j, hij, hb⟩ := d.trans A hA
  refine ⟨i, j, hij, fun b => ⟨hb b, ?_⟩⟩
  rintro (h1 | h1)
  · have : b = 1 := d.θ.injective (by rw [h1, map_one])
    rw [this]
    exact A.one_mem
  · obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hb₀P : b₀ ∈ P := hA.2 hb₀
    have hθ₀ : d.θ ⟨b₀, hb₀P⟩ = Equiv.swap i j := by
      rcases hb ⟨b₀, hb₀P⟩ hb₀ with h2 | h2
      · exfalso
        apply hb₀1
        have : (⟨b₀, hb₀P⟩ : ↥P) = 1 := d.θ.injective (by rw [h2, map_one])
        exact Subtype.ext (show b₀ = 1 from congrArg Subtype.val this)
      · exact h2
    have : b = ⟨b₀, hb₀P⟩ := d.θ.injective (by rw [h1, hθ₀])
    rw [this]
    exact hb₀

omit [Finite V] in
theorem SymCore.pt_of_hyp42 (d : SymCore D P m) (h : Hyp42 P D T M) :
    ∃ i₀ : Fin m, ∀ x : ↥P, (x : MulAut V) ∈ M ↔ d.θ x i₀ = i₀ := by
  classical
  set θ := d.θ with hθdef
  set T' : Subgroup (Equiv.Perm (Fin m)) := (T.subgroupOf P).map θ.toMonoidHom with hT'
  set M' : Subgroup (Equiv.Perm (Fin m)) := (M.subgroupOf P).map θ.toMonoidHom with hM'
  have hTP : T ≤ P := h.syl.1
  have hmemT : ∀ x : ↥P, θ x ∈ T' ↔ (x : MulAut V) ∈ T := fun x => by
    rw [hT', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := θ.injective hyx
      subst this
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmemM : ∀ x : ↥P, θ x ∈ M' ↔ (x : MulAut V) ∈ M := fun x => by
    rw [hM', Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := θ.injective hyx
      subst this
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hT2 : IsPGroup 2 T' :=
    (h.syl.2.1.comap_subtype (K := P)).map θ.toMonoidHom
  have hTidx : ¬ 2 ∣ T'.index := by
    have h1 : T'.index = (T.subgroupOf P).index := Subgroup.index_map_equiv (T.subgroupOf P) θ
    rw [h1]
    exact h.syl.2.2
  have hTM : T' ≤ M' := fun z hz => by
    obtain ⟨x, rfl⟩ := θ.surjective z
    exact (hmemM x).2 (h.le_M ((hmemT x).1 hz))
  have hMtop : M' ≠ ⊤ := by
    intro htop
    have hPM : P ≤ M := fun g hg => (hmemM ⟨g, hg⟩).1 (by rw [htop]; exact Subgroup.mem_top _)
    have hMP : M = P := le_antisymm h.M_le hPM
    apply h.ne_core
    refine Set.Subset.antisymm (fun A hA => ?_) (fun A hA => hA.1)
    refine ⟨hA, fun g hg => ?_⟩
    rw [hMP, conjSub_self_of_mem hg]
    exact h.le A hA
  have hleT : ∀ A : Subgroup (MulAut V), A ∈ dInter D P → ∀ i j : Fin m, i ≠ j →
      (∀ b : ↥P, (b : MulAut V) ∈ A ↔ θ b = 1 ∨ θ b = Equiv.swap i j) →
      (A ≤ T ↔ Equiv.swap i j ∈ T') := by
    intro A hA i j hij hb
    constructor
    · intro hAT
      obtain ⟨b₀, hb₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (h.ne_bot A hA.1)
      have hb₀P : (b₀ : MulAut V) ∈ P := hA.2 b₀.2
      have hθ : θ ⟨b₀, hb₀P⟩ = Equiv.swap i j := by
        rcases (hb ⟨b₀, hb₀P⟩).1 b₀.2 with h1 | h1
        · exfalso
          apply hb₀
          have : (⟨b₀, hb₀P⟩ : ↥P) = 1 := θ.injective (by rw [h1, map_one])
          exact Subtype.ext (show (b₀ : MulAut V) = 1 from congrArg Subtype.val this)
        · exact h1
      rw [← hθ, hmemT]
      exact hAT b₀.2
    · intro hs a ha
      have haP : a ∈ P := hA.2 ha
      rcases (hb ⟨a, haP⟩).1 ha with h1 | h1
      · have : (⟨a, haP⟩ : ↥P) = 1 := θ.injective (by rw [h1, map_one])
        have ha1 : a = 1 := congrArg Subtype.val this
        rw [ha1]
        exact T.one_mem
      · exact (hmemT ⟨a, haP⟩).1 (by rw [h1]; exact hs)
  have hconjpair : ∀ (A : Subgroup (MulAut V)) (i j : Fin m)
      (_ : ∀ b : ↥P, (b : MulAut V) ∈ A ↔ θ b = 1 ∨ θ b = Equiv.swap i j) (y : ↥P) (b : ↥P),
      (b : MulAut V) ∈ conjSub (y : MulAut V) A ↔
        θ b = 1 ∨ θ b = Equiv.swap (θ y i) (θ y j) := by
    intro A i j hb y b
    rw [mem_conjSub_iff]
    have e1 : θ (y⁻¹ * b * y) = (θ y)⁻¹ * θ b * θ y := by rw [map_mul, map_mul, map_inv]
    have hcoe : ((y⁻¹ * b * y : ↥P) : MulAut V) =
        (y : MulAut V)⁻¹ * (b : MulAut V) * (y : MulAut V) := rfl
    have h2 := hb (y⁻¹ * b * y)
    rw [hcoe, e1] at h2
    rw [h2, Equiv.swap_apply_apply]
    constructor
    · rintro (h1 | h1)
      · left
        calc θ b = θ y * ((θ y)⁻¹ * θ b * θ y) * (θ y)⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · right
        calc θ b = θ y * ((θ y)⁻¹ * θ b * θ y) * (θ y)⁻¹ := by group
          _ = θ y * Equiv.swap i j * (θ y)⁻¹ := by rw [h1]
    · rintro (h1 | h1)
      · left
        rw [h1]
        group
      · right
        rw [h1]
        group
  have hN : ∀ x : Equiv.Perm (Fin m),
      (∀ i j : Fin m, i ≠ j → (Equiv.swap i j ∈ T' ↔ Equiv.swap (x i) (x j) ∈ T')) → x ∈ M' := by
    intro x hx
    obtain ⟨y, rfl⟩ := θ.surjective x
    rw [hmemM]
    refine h.normSet_le ⟨y.2, fun A' => ?_⟩
    have key : ∀ A : Subgroup (MulAut V), A ∈ dInter D P →
        conjSub (y : MulAut V) A ∈ dInter D P ∧ (A ≤ T ↔ conjSub (y : MulAut V) A ≤ T) := by
      intro A hA
      obtain ⟨i, j, hij, hb⟩ := d.exists_swap_of_mem hA (h.ne_bot A hA.1)
      have hAD' : conjSub (y : MulAut V) A ∈ D := h.conj_mem A hA.1 y y.2
      have hAP' : conjSub (y : MulAut V) A ≤ P := h.le _ hAD'
      refine ⟨⟨hAD', hAP'⟩, ?_⟩
      have hb' := hconjpair A i j hb y
      have hij' : θ y i ≠ θ y j := fun e => hij ((θ y).injective e)
      rw [hleT A hA i j hij hb, hleT _ ⟨hAD', hAP'⟩ _ _ hij' hb']
      exact hx i j hij
    constructor
    · intro hA'
      have hA'P : A' ∈ dInter D P := ⟨hA'.1, hA'.2.trans hTP⟩
      obtain ⟨hc, hiff⟩ := key A' hA'P
      exact ⟨hc.1, hiff.1 hA'.2⟩
    · intro hA'
      have hA'D : A' ∈ D := by
        have := h.conj_mem _ hA'.1 (y : MulAut V)⁻¹ (P.inv_mem y.2)
        rwa [FourTwoTools.conjSub_inv_conjSub] at this
      obtain ⟨hc, hiff⟩ := key A' ⟨hA'D, h.le A' hA'D⟩
      exact ⟨hA'D, hiff.2 hA'.2⟩
  have hC : ∀ x : Equiv.Perm (Fin m),
      (∀ v : coreMod m, (∀ t ∈ T', coreAct m t v = v) → coreAct m x v = v) → x ∈ M' := by
    intro x hx
    obtain ⟨y, rfl⟩ := θ.surjective x
    rw [hmemM]
    refine h.cen_le ⟨y.2, fun v hv => ?_⟩
    have hvtop : v ∈ commV P ⊔ fixV P := by
      rw [d.top]
      exact Subgroup.mem_top _
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hvtop
    have hcP : ∀ g ∈ P, g c = c := hc
    have hTw : ∀ t ∈ T, t w = w := by
      intro t ht
      have h1 := hv t ht
      rw [map_mul, hcP t (hTP ht)] at h1
      exact mul_right_cancel h1
    have hinj : Function.Injective d.β := (MonoidHom.ker_eq_bot_iff d.β).1 d.ker
    have hfix : ∀ t' ∈ T', coreAct m t' (d.β ⟨w, hw⟩) = d.β ⟨w, hw⟩ := by
      intro t' ht'
      obtain ⟨t, rfl⟩ := θ.surjective t'
      have ht : (t : MulAut V) ∈ T := (hmemT t).1 ht'
      have hmem : (t : MulAut V) w ∈ commV P := d.inv _ t.2 w hw
      rw [← d.equiv t ⟨w, hw⟩ hmem]
      congr 1
      exact Subtype.ext (hTw _ ht)
    have hxw := hx _ hfix
    have hyw : (y : MulAut V) w = w := by
      have hmem : (y : MulAut V) w ∈ commV P := d.inv _ y.2 w hw
      have := d.equiv y ⟨w, hw⟩ hmem
      rw [hxw] at this
      exact congrArg Subtype.val (hinj this)
    rw [map_mul, hyw, hcP _ y.2]
  obtain ⟨i₀, hi₀⟩ :=
    exists_point_stabilizer_of_overgroup d.odd d.three_le hT2 hTidx hTM hMtop hN hC
  exact ⟨i₀, fun x => (hmemM x).symm.trans (hi₀ (θ x))⟩

end Point

theorem symData_of_chain {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    {T M : Subgroup (MulAut V)} (h : Hyp42 P D T M) (hV : ∀ v : V, v ^ 2 = 1) (hconn : ConnD D)
    {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (x : ℕ → MulAut V) (u : ℕ → V)
    (hx : ∀ i < k, IsTransv (x i) (u i)) (hxD : ∀ i < k, Subgroup.zpowers (x i) ∈ D)
    (hadj : ∀ i, i + 1 < k → x i * x (i + 1) ≠ x (i + 1) * x i)
    (hfar : ∀ i j, i + 2 ≤ j → j < k → x i * x j = x j * x i)
    (hne : ∀ i < k, ∀ j < k, i ≠ j → x i ≠ x j)
    (hgen : Subgroup.closure (x '' Set.Iio k) = P) : Nonempty (SymData M D P (k + 1)) := by
  obtain ⟨d, -⟩ := symCore_of_chain h.toHyp41 hV hconn hk hk2 x u hx hxD hadj hfar hne hgen
  exact ⟨{ toSymCore := d, pt := d.pt_of_hyp42 h }⟩

end CFSG.CGT.PushingUpLit.BHS
