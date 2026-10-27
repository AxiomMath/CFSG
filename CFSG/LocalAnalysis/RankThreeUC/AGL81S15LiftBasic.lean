module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem pCore_le_gnC_aux1 {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.pCore 2 X ≤ T := by
  have hidx : ¬ 2 ∣ T.index := by
    have h : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at h
  exact (CFSG.pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal (hT.2.1.toSylow hidx)

theorem pCore_le_gnC_aux2 {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.Quasithin.omegaOneCenterOf T ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
  have hPT : CFSG.pCore 2 X ≤ T := pCore_le_gnC_aux1 hT
  unfold CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf CFSG.Quasithin.centerOf
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  have hxc : x ∈ Subgroup.centralizer (T : Set X) := hx.1.2
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_iff.1 hxc h (hPT hh)

theorem pCore_le_gnC {T : Subgroup X} (hX : GNSetting X T) : CFSG.pCore 2 X ≤ gnC T := by
  have hV : gnV T ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) :=
    Subgroup.normalClosure_le_normal (pCore_le_gnC_aux2 hX.sylow)
  exact Subgroup.le_centralizer_iff.2 hV

theorem isC2_normalizer_aux0 {N : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) : N ≤ CFSG.pCore 2 X :=
  le_sSup ⟨inferInstance, hN⟩

theorem isC2_normalizer_aux1 {N : Subgroup X} {n g : X} (hn : n ∈ N)
    (hg : g ∈ Subgroup.normalizer (N : Set X)) : ⁅n, g⁆ ∈ N := by
  have h1 : g * n⁻¹ * g⁻¹ ∈ N := ((Subgroup.mem_normalizer_iff.1 hg) n⁻¹).1 (N.inv_mem hn)
  have h2 : ⁅n, g⁆ = n * (g * n⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [h2]
  exact N.mul_mem hn h1

theorem isC2_normalizer_aux2 {H K : Subgroup X} (hHK : CFSG.Open.IsSubnormal H K) :
    ∀ N : Subgroup X, K ≤ Subgroup.normalizer (N : Set X) → N ≤ K → IsPGroup 2 N →
      ∀ h ∈ H, Odd (orderOf h) → ⁅N, Subgroup.zpowers h⁆ ≤ H := by
  induction hHK with
  | refl H =>
    intro N hKN hNK hN h hh hodd
    refine le_trans ?_ hNK
    rw [Subgroup.commutator_le]
    intro n hn g hg
    exact isC2_normalizer_aux1 hn (hKN ((Subgroup.zpowers_le.2 hh) hg))
  | @step H M K hHM hnorm hMK ih =>
    intro N hKN hNK hN h hh hodd
    have hMK' : M ≤ K := hMK.le
    have hh_norm : h ∈ Subgroup.normalizer (N : Set X) := hKN (hMK' (hHM hh))
    have h1 : ⁅N, Subgroup.zpowers h⁆ ≤ M := ih N hKN hNK hN h (hHM hh) hodd
    have h2 : ⁅N, Subgroup.zpowers h⁆ ≤ N := by
      rw [Subgroup.commutator_le]
      intro n hn g hg
      exact isC2_normalizer_aux1 hn (hKN (hMK' (hHM ((Subgroup.zpowers_le.2 hh) hg))))
    have h3 : ⁅⁅N, Subgroup.zpowers h⁆, Subgroup.zpowers h⁆ = ⁅N, Subgroup.zpowers h⁆ :=
      (kCop_holds X N h hN hh_norm hodd).2
    have h4 : ⁅N ⊓ M, Subgroup.zpowers h⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro n hn g hg
      have hgH : g ∈ H := (Subgroup.zpowers_le.2 hh) hg
      have hnorm' := (Subgroup.normal_subgroupOf_iff hHM).1 hnorm
      have h5 : ⁅n, g⁆ = (n * g * n⁻¹) * g⁻¹ := by rw [commutatorElement_def]
      rw [h5]
      exact H.mul_mem (hnorm' g n hgH hn.2) (H.inv_mem hgH)
    calc ⁅N, Subgroup.zpowers h⁆ = ⁅⁅N, Subgroup.zpowers h⁆, Subgroup.zpowers h⁆ := h3.symm
      _ ≤ ⁅N ⊓ M, Subgroup.zpowers h⁆ := Subgroup.commutator_mono (le_inf h2 h1) le_rfl
      _ ≤ H := h4

theorem isC2_normalizer {L : Subgroup X} (hL : IsC2 L) (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N) : N ≤ Subgroup.normalizer (L : Set X) ∧ ⁅L, N⁆ ≤ O2In L := by
  have key : ∀ h ∈ L, Odd (orderOf h) → ⁅N, Subgroup.zpowers h⁆ ≤ L := fun h hh hodd =>
    isC2_normalizer_aux2 hL.1 N Subgroup.le_normalizer_of_normal le_top hN h hh hodd
  have fwd : ∀ n ∈ N, ∀ x ∈ L, n * x * n⁻¹ ∈ L := by
    intro n hn
    have hle : L ≤ L.comap (MulAut.conj n).toMonoidHom := by
      calc L = oddHull L := hL.2.1.symm
        _ ≤ L.comap (MulAut.conj n).toMonoidHom := by
          unfold oddHull
          refine (Subgroup.closure_le _).2 ?_
          rintro h ⟨hhL, hodd⟩
          show n * h * n⁻¹ ∈ L
          have hc : ⁅n, h⁆ ∈ L :=
            key h hhL hodd (Subgroup.commutator_mem_commutator hn (Subgroup.mem_zpowers h))
          have h2 : n * h * n⁻¹ = ⁅n, h⁆ * h := by rw [commutatorElement_def]; group
          rw [h2]
          exact L.mul_mem hc hhL
    intro x hx
    exact hle hx
  have hnorm : N ≤ Subgroup.normalizer (L : Set X) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => fwd n hn x hx, fun hx => ?_⟩
    have h1 := fwd n⁻¹ (N.inv_mem hn) _ hx
    simpa [mul_assoc] using h1
  refine ⟨hnorm, ?_⟩
  unfold O2In
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx n hn
    have h2 : ⁅x, n⁆ = x * (n * x⁻¹ * n⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact L.mul_mem hx (fwd n hn x⁻¹ (L.inv_mem hx))
  · exact le_trans (Subgroup.commutator_le_right L N) (isC2_normalizer_aux0 hN)

theorem isC2_eq_of_barO2_eq_aux1 {L : Subgroup X} {l c : X} (hl : l ∈ L)
    (hc : c ∈ Subgroup.normalizer (L : Set X)) (n : ℕ) : ∃ l' ∈ L, (l * c) ^ n = l' * c ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hcn : c ^ n ∈ Subgroup.normalizer (L : Set X) := Subgroup.pow_mem _ hc n
    have h1 : c ^ n * l * (c ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hcn l).1 hl
    refine ⟨l' * (c ^ n * l * (c ^ n)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem isC2_eq_of_barO2_eq_aux2 {L : Subgroup X} (hL : IsC2 L) {x : X}
    (hx : x ∈ L ⊔ CFSG.pCore 2 X) (hodd : Odd (orderOf x)) : x ∈ L := by
  have hnorm : CFSG.pCore 2 X ≤ Subgroup.normalizer (L : Set X) :=
    (isC2_normalizer hL (CFSG.pCore 2 X) CFSG.pCore_isPGroup).1
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨c, hc⟩
  have hck : c ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', hpow⟩ := isC2_eq_of_barO2_eq_aux1 hl (hnorm hc) (2 ^ k)
  rw [hck, mul_one] at hpow
  have hxk : (l * c) ^ (2 ^ k) ∈ L := hpow ▸ hl'
  have hcop : Nat.Coprime (2 ^ k) (orderOf (l * c)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : ((2 ^ k : ℕ) : ℤ) * u + (orderOf (l * c) : ℤ) * v = 1 := by
    rw [mul_comm ((2 ^ k : ℕ) : ℤ) u, mul_comm (orderOf (l * c) : ℤ) v]
    exact huv
  have e : l * c = ((l * c) ^ (2 ^ k)) ^ u := by
    calc l * c = (l * c) ^ (1 : ℤ) := (zpow_one _).symm
      _ = (l * c) ^ (((2 ^ k : ℕ) : ℤ) * u + (orderOf (l * c) : ℤ) * v) := by rw [huv']
      _ = ((l * c) ^ ((2 ^ k : ℕ) : ℤ)) ^ u * ((l * c) ^ (orderOf (l * c) : ℤ)) ^ v := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = ((l * c) ^ (2 ^ k)) ^ u := by
        rw [zpow_natCast, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
  rw [e]
  exact Subgroup.zpow_mem L hxk u

theorem isC2_eq_of_barO2_eq {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L') (h : barO2 L = barO2 L') : L = L' := by
  have key : ∀ {A B : Subgroup X}, IsC2 A → IsC2 B → barO2 A = barO2 B → A ≤ B := by
    intro A B hA hB hAB
    calc A = oddHull A := hA.2.1.symm
      _ ≤ B := by
        unfold oddHull
        refine (Subgroup.closure_le B).2 ?_
        rintro x ⟨hxA, hodd⟩
        have hxbar : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈ barO2 B := by
          rw [← hAB]
          exact ⟨x, hxA, rfl⟩
        obtain ⟨y, hyB, hy⟩ := hxbar
        have hyx : y⁻¹ * x ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hy
        have hxsup : x ∈ B ⊔ CFSG.pCore 2 X := by
          have h1 : x = y * (y⁻¹ * x) := by group
          rw [h1]
          exact Subgroup.mul_mem_sup hyB hyx
        exact isC2_eq_of_barO2_eq_aux2 hB hxsup hodd
  exact le_antisymm (key hL hL' h) (key hL' hL h.symm)

theorem isC2_commute_of_ne {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L') (hne : L ≠ L') : ⁅barO2 L, barO2 L'⁆ = ⊥ :=
  kComp_holds.1 (X ⧸ CFSG.pCore 2 X) (barO2 L) (barO2 L') hL.component hL'.component
    (fun h => hne (isC2_eq_of_barO2_eq hL hL' h))

theorem isC2_barO2_le_or_commute {L : Subgroup X} (hL : IsC2 L) (N : Subgroup X) [N.Normal] : barO2 L ≤ barO2 N ∨ ⁅barO2 L, barO2 N⁆ = ⊥ :=
  kComp_holds.2 (X ⧸ CFSG.pCore 2 X) (barO2 L) (barO2 N)
    (Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective _)) hL.component

theorem liftOf_unique_aux1 {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A ⊤) : ⁅A, A⁆ ≠ ⊥ := by
  intro h1
  have hs : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hA.2.2.2
  have hcen : Subgroup.center ↥A = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 : ⁅(g : G), (z : G)⁆ ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator g.2 z.2
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact Subtype.ext h2
  have hsub : Subsingleton (↥A ⧸ Subgroup.center ↥A) := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.2 (by rw [hcen]; exact Subgroup.mem_top _)⟩
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem liftOf_unique_aux2 {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A ⊤) : A ≠ ⊥ := by
  intro h
  apply liftOf_unique_aux1 hA
  rw [h]
  exact Subgroup.commutator_bot_left _

theorem liftOf_unique {T L L' : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (h : LiftOf T L Ls) (h' : LiftOf T L' Ls) : L = L' := by
  by_contra hne
  have hcomm := isC2_commute_of_ne h.1 h'.1 hne
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφ : ∀ A : Subgroup X, (barO2 A).map φ = A.map (toStar T) := by
    intro A
    unfold barO2
    rw [Subgroup.map_map]
    congr 1
  have h1 := congrArg (Subgroup.map φ) hcomm
  rw [Subgroup.map_commutator, hφ, hφ, h.2, h'.2, Subgroup.map_bot] at h1
  exact liftOf_unique_aux1 hLs h1

theorem liftOf_central_ext_aux1 {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {M : Subgroup Q} (hM : M.Normal) : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hp, hs⟩ := hQ
  have := hM.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (M.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have hsup : M ⊔ Subgroup.center Q = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have hcomm : commutator Q ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem liftOf_central_ext {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (h : LiftOf T L Ls) : (L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ (Subgroup.center ↥(barO2 L)).map (barO2 L).subtype ∧ Ls.comap (toStar T) = L ⊔ gnC T := by
  refine ⟨?_, ?_⟩
  · have hMQ : (L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ barO2 L :=
      Subgroup.map_mono inf_le_left
    have hnormal :
        (((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))).subgroupOf (barO2 L)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hMQ]
      rintro n g ⟨b, hb, rfl⟩ ⟨a, ha, rfl⟩
      refine ⟨a * b * a⁻¹, ⟨L.mul_mem (L.mul_mem ha hb.1) (L.inv_mem ha), ?_⟩, by simp⟩
      exact (gnC_normal T).conj_mem b hb.2 a
    rcases liftOf_central_ext_aux1 h.1.component.2.2 hnormal with hcen | htop
    · intro m hm
      have hmQ : m ∈ barO2 L := hMQ hm
      have hm' : (⟨m, hmQ⟩ : ↥(barO2 L)) ∈
          ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))).subgroupOf (barO2 L) := hm
      exact ⟨⟨m, hmQ⟩, hcen hm', rfl⟩
    · exfalso
      have hLC : L ≤ gnC T := by
        intro a ha
        have hmem : (⟨QuotientGroup.mk' (CFSG.pCore 2 X) a, ⟨a, ha, rfl⟩⟩ : ↥(barO2 L)) ∈
            ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))).subgroupOf (barO2 L) := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨b, hb, hba⟩ := hmem
        have hba' : b⁻¹ * a ∈ CFSG.pCore 2 X := QuotientGroup.eq.1 hba
        have h2 : a = b * (b⁻¹ * a) := by group
        rw [h2]
        exact (gnC T).mul_mem hb.2 (pCore_le_gnC hX hba')
      have hLs_bot : Ls = ⊥ := by
        rw [← h.2, eq_bot_iff]
        rintro _ ⟨a, ha, rfl⟩
        exact (QuotientGroup.eq_one_iff a).2 (hLC ha)
      exact liftOf_unique_aux2 hLs hLs_bot
  · have h2 := Subgroup.comap_map_eq (toStar T) L
    rw [h.2, QuotientGroup.ker_mk'] at h2
    exact h2

theorem liftOf_conj_aux1 {G : Type*} [Group G] {A : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj y).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hy a).1 ha
  · intro hz
    have h1 : y⁻¹ * z * y ∈ A := by
      have h2 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hy) z).1 hz
      simpa using h2
    refine ⟨y⁻¹ * z * y, h1, ?_⟩
    show y * (y⁻¹ * z * y) * y⁻¹ = z
    group

theorem liftOf_conj_aux2 {L : Subgroup X} (σ : X ≃* X) :
    (oddHull L).map σ.toMonoidHom ≤ oddHull (L.map σ.toMonoidHom) := by
  unfold oddHull
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨a, ⟨haL, hodd⟩, rfl⟩
  refine ⟨⟨a, haL, rfl⟩, ?_⟩
  show Odd (orderOf (σ.toMonoidHom a))
  rw [orderOf_injective σ.toMonoidHom σ.injective a]
  exact hodd

theorem liftOf_conj_aux3 {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A ⊤) (τ : G ≃* G) :
    CFSG.Open.IsComponentOf (A.map τ.toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h1 := hA.2.1.map τ.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ τ.surjective] at h1
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (A.equivMapOfInjective τ.toMonoidHom τ.injective).symm hA.2.2

theorem liftOf_conj_aux4 {L : Subgroup X} (hL : IsC2 L) (x : X) :
    IsC2 (L.map (MulAut.conj x).toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hL.1.map (MulAut.conj x).toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective] at h1
  · apply le_antisymm
    · unfold oddHull
      exact (Subgroup.closure_le _).2 (fun y hy => hy.1)
    · calc L.map (MulAut.conj x).toMonoidHom
          = (oddHull L).map (MulAut.conj x).toMonoidHom := by rw [hL.2.1]
        _ ≤ oddHull (L.map (MulAut.conj x).toMonoidHom) := liftOf_conj_aux2 (MulAut.conj x)
  · have hτ : barO2 (L.map (MulAut.conj x).toMonoidHom) =
        (barO2 L).map (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).toMonoidHom := by
      unfold barO2
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    show CFSG.Open.IsComponentOf (barO2 (L.map (MulAut.conj x).toMonoidHom)) ⊤
    rw [hτ]
    exact liftOf_conj_aux3 hL.component _

theorem liftOf_conj {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤) (h : LiftOf T L Ls) (x : X) (hx : toStar T x ∈ Subgroup.normalizer (Ls : Set (X ⧸ gnC T))) : L.map (MulAut.conj x).toMonoidHom = L := by
  have hL' : LiftOf T (L.map (MulAut.conj x).toMonoidHom) Ls := by
    refine ⟨liftOf_conj_aux4 h.1 x, ?_⟩
    have hcomp : (toStar T).comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (toStar T x)).toMonoidHom.comp (toStar T) := by
      ext a
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h.2]
    exact liftOf_conj_aux1 hx
  exact liftOf_unique hX hLs hL' h

theorem centre_barO2_odd {L : Subgroup X} (hL : IsC2 L) : Odd (Nat.card (Subgroup.center ↥(barO2 L))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥(barO2 L)) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzsq : z ^ 2 = 1 := by
    have h3 := pow_orderOf_eq_one z
    rwa [hz] at h3
  have hw2 : z.1.1 ^ 2 = 1 := by
    have h3 := congrArg (fun t : ↥(Subgroup.center ↥(barO2 L)) => t.1.1) hzsq
    simpa using h3
  have hw1 : z.1.1 ≠ 1 := by
    intro h1
    have h3 : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [h3, orderOf_one] at hz
    omega
  obtain ⟨ℓ, hℓL, hℓ⟩ := z.1.2
  have hcent : ∀ a ∈ L, QuotientGroup.mk' (CFSG.pCore 2 X) a * z.1.1 =
      z.1.1 * QuotientGroup.mk' (CFSG.pCore 2 X) a := by
    intro a ha
    have h3 := Subgroup.mem_center_iff.1 z.2 ⟨QuotientGroup.mk' (CFSG.pCore 2 X) a, ⟨a, ha, rfl⟩⟩
    exact congrArg Subtype.val h3
  let R₀ : Subgroup X := L ⊓ (Subgroup.zpowers z.1.1).comap (QuotientGroup.mk' (CFSG.pCore 2 X))
  have hR₀2 : IsPGroup 2 R₀ := by
    intro g
    obtain ⟨g, hgL, hgw⟩ := g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgw
    have hsq : (QuotientGroup.mk' (CFSG.pCore 2 X) g) ^ 2 = 1 := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
    have hmem : g ^ 2 ∈ CFSG.pCore 2 X := by
      rw [← QuotientGroup.eq_one_iff]
      simpa using hsq
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨g ^ 2, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h3 ⊢
    rw [pow_succ', pow_mul]
    exact h3
  have hR₀norm : (R₀.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_left : R₀ ≤ L)]
    rintro r a ⟨hrL, hrw⟩ haL
    refine ⟨L.mul_mem (L.mul_mem haL hrL) (L.inv_mem haL), ?_⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hrw
    have hc : Commute (QuotientGroup.mk' (CFSG.pCore 2 X) a) z.1.1 := hcent a haL
    have hcj : Commute (QuotientGroup.mk' (CFSG.pCore 2 X) a) (z.1.1 ^ j) := hc.zpow_right j
    show QuotientGroup.mk' (CFSG.pCore 2 X) (a * r * a⁻¹) ∈ Subgroup.zpowers z.1.1
    rw [map_mul, map_mul, map_inv, ← hj, hcj.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z.1.1) j
  have hsub : CFSG.Open.IsSubnormal R₀ ⊤ := CFSG.Open.IsSubnormal.step inf_le_left hR₀norm hL.1
  have hle : R₀ ≤ CFSG.pCore 2 X := kSubn_holds X R₀ hsub hR₀2
  have hℓR : ℓ ∈ R₀ := by
    refine ⟨hℓL, ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 X) ℓ ∈ Subgroup.zpowers z.1.1
    rw [hℓ]
    exact Subgroup.mem_zpowers z.1.1
  have h3 : QuotientGroup.mk' (CFSG.pCore 2 X) ℓ = 1 := (QuotientGroup.eq_one_iff ℓ).2 (hle hℓR)
  exact hw1 (hℓ ▸ h3)

end CFSG.LocalAnalysis.RankThreeUC.S15
