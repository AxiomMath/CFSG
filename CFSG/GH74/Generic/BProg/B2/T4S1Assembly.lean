module

public import CFSG.GH74.Generic.BProg.B2.T4ElimAssembly
public import CFSG.GH74.Generic.BProg.B2.T4Basic
public import CFSG.GH74.Generic.BProg.B2.Lemma172
public import CFSG.GH74.Generic.BProg.B2.T3S1Bar
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out

public section

namespace CFSG.GH74.Generic.BProg.B2.T4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

namespace T4S1

section Abstract

variable {N : Type} [Group N] [Finite N]

theorem mem_of_mul_self_of_out16 (hG : Gen4 N) {H : Subgroup N} [H.Normal] (hs : IsSimpleGroup ↥H)
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (h16 : GenLocL5Gen.Out16 ↥H)
    {v : N} (hv : v * v = 1) : v ∈ H := by
  classical
  by_contra hvH
  let φ : N →* MulAut ↥H := MulAut.conjNormal
  have hφa : ∀ (n : N) (h : ↥H), ((φ n h : ↥H) : N) = n * h * n⁻¹ := fun n h => by
    simp [φ, MulAut.conjNormal_apply]
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    apply hfaith n
    intro h hh
    have h1 := hφa n ⟨h, hh⟩
    rw [hn] at h1
    have h2 : n * h * n⁻¹ = h := h1.symm
    calc n * h = n * h * n⁻¹ * n := by group
      _ = h * n := by rw [h2]
  set A : Subgroup N := Subgroup.zpowers v with hAdef
  have hA : CFSG.IsElementaryAbelian 2 ↥A := by
    have hA' : CFSG.IsElementaryAbelian 2 ↥A := by
      refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
      · intro a ha b hb
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_zpow_self v i j).eq
      · intro a ha
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [← zpow_add, ← two_mul, zpow_mul, show v ^ (2 : ℤ) = 1 by rw [zpow_two, hv], one_zpow]
    exact hA'
  let α : ↥A →* MulAut ↥H := φ.comp A.subtype
  have hout : ¬ α.range ≤ (MulAut.conj : ↥H →* MulAut ↥H).range := by
    intro hle
    obtain ⟨h₀, hh₀⟩ := hle ⟨⟨v, Subgroup.mem_zpowers v⟩, rfl⟩
    apply hvH
    have hc : ∀ h ∈ H, ((h₀ : N)⁻¹ * v) * h = h * ((h₀ : N)⁻¹ * v) := by
      intro h hh
      have h1 := congrArg (fun f : MulAut ↥H => ((f ⟨h, hh⟩ : ↥H) : N)) hh₀
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : (h₀ : N) * h * (h₀ : N)⁻¹ = v * h * v⁻¹ := by
        rw [h1]
        exact hφa v ⟨h, hh⟩
      calc ((h₀ : N)⁻¹ * v) * h = (h₀ : N)⁻¹ * (v * h * v⁻¹) * v := by group
        _ = (h₀ : N)⁻¹ * ((h₀ : N) * h * (h₀ : N)⁻¹) * v := by rw [h2]
        _ = h * ((h₀ : N)⁻¹ * v) := by group
    have h3 := hfaith _ hc
    have : v = (h₀ : N) := by
      have := congrArg (fun z => (h₀ : N) * z) h3
      simpa using this
    rw [this]
    exact h₀.2
  have hsect : SectionalTwoRankLE ↥(innJoin α) 4 := by
    have hle : innJoin α ≤ φ.range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨h, rfl⟩
        refine ⟨(h : N), ?_⟩
        ext k
        rw [hφa]
        simp [MulAut.conj_apply]
      · rintro _ ⟨a, rfl⟩
        exact ⟨(a : N), rfl⟩
    let e : N ≃* ↥φ.range := MonoidHom.ofInjective hφ
    have hinj : Function.Injective (e.symm.toMonoidHom.comp (Subgroup.inclusion hle)) :=
      e.symm.injective.comp (Subgroup.inclusion_injective hle)
    exact SectionalTwoRankLE.of_injective _ hinj hG
  exact GenLocL5Gen.not_sectional_of_out16 hs h16 hA α hout hsect

end Abstract

@[expose] def PuL5InvE8 : Prop :=
  ∀ (J : Type) [Group J] [Finite J], PuL5 J → ∀ E : Subgroup J, CFSG.IsElementaryAbelian 2 ↥E →
    Nat.card ↥E = 8 → ∀ v : J, v * v = 1 → v ≠ 1 → ∃ g : J, g * v * g⁻¹ ∈ E

@[expose] def S1Prop151 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A M P Q →
    Stage2Concl1 x K M Q H → Stage3A x A M H → QShape1 (↥K ⧸ pPrimeCore 2 ↥K) →
      PuL5 ↥(barIn M H) → Prop151For A M

section Group

variable {G : Type} [Group G] [Finite G]

theorem mk_mem_barIn {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h3 : Stage3A x A M H) (hL5 : PuL5 ↥(barIn M H)) {v : G} (hvM : v ∈ M) (hv : v * v = 1) :
    (QuotientGroup.mk (⟨v, hvM⟩ : ↥M) : Mbar M) ∈ barIn M H := by
  have hG4 : Gen4 (Mbar M) := Gen4.quotient (pPrimeCore 2 ↥M) (Gen4.subgroup M hs.hyp.gen4)
  have hHn : (barIn M H).Normal := by
    rw [h3.H_simple.1]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  refine mem_of_mul_self_of_out16 hG4 h3.H_simple.2 (Prop31.faithful_of_simple hs h3)
    (GenLocL5Out.out16_of_puL5 hL5) ?_
  rw [← QuotientGroup.mk_mul]
  have : (⟨v, hvM⟩ : ↥M) * ⟨v, hvM⟩ = 1 := Subtype.ext hv
  rw [this, QuotientGroup.mk_one]


theorem A_le_K {x : G} {K A M P Q : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) : A ≤ K := by
  obtain ⟨-, -, -, hcase⟩ := hs.src
  rcases hcase with ⟨hAK, -⟩ | ⟨_, -, -, -, -, -, hshape⟩
  · exact hAK
  · exact (B1.PilotS3.not_qShape1_of_center_trivial hk1
      (centerlessS345 _ (TwoThin.isQuasisimple_hat hs.pair.1.1.1.2.2) hshape)).elim

theorem barA_E8 {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) :
    T3S1.IsE8 ((barIn M A).subgroupOf (barIn M H)) ∧ barIn M A ≤ barIn M H :=
  T3S1.isE8_barA h1.H_min.2.1.1 ((A_le_K hs hk1).trans h1.H_min.1) hs.src.2.1 hs.src.2.2.1

omit [Finite G]
  in
theorem orderOf_conj_two {y g : G} (hy : orderOf y = 2) : orderOf (g⁻¹ * y * g) = 2 := by
  have e : g⁻¹ * y * g = (MulAut.conj g⁻¹) y := by simp
  rw [e, MulEquiv.orderOf_eq]
  exact hy

theorem exists_conj_A (hInv : PuL5InvE8) {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H)
    (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hL5 : PuL5 ↥(barIn M H)) {v : G} (hvM : v ∈ M)
    (hv2 : orderOf v = 2) : ∃ a ∈ A, a ≠ 1 ∧ ∃ m ∈ M, m⁻¹ * a * m = v := by
  have hvv : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv2, sq] at this
  set vb : Mbar M := QuotientGroup.mk (⟨v, hvM⟩ : ↥M) with hvb
  have hvH : vb ∈ barIn M H := mk_mem_barIn hs h3 hL5 hvM hvv
  have hvb2 : orderOf vb = 2 := Prop31.orderOf_mk_involution hvM hv2
  have hvbb : vb * vb = 1 := by
    have := pow_orderOf_eq_one vb
    rwa [hvb2, sq] at this
  have hvb1 : vb ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hvb2
    omega
  obtain ⟨hE8, -⟩ := barA_E8 hs h1 hk1
  obtain ⟨g, hg⟩ := hInv ↥(barIn M H) hL5 _ hE8.1 hE8.2 ⟨vb, hvH⟩ (Subtype.ext hvbb)
    (fun h => hvb1 (congrArg Subtype.val h))
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨a', ha', hae⟩ := hg
  have haA : (a' : G) ∈ A := Subgroup.mem_subgroupOf.1 ha'
  have hae' : (QuotientGroup.mk a' : Mbar M) = (g : Mbar M) * vb * (g : Mbar M)⁻¹ := by
    have h := hae
    rw [QuotientGroup.mk'_apply] at h
    rw [h]
    simp
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hs.src.2.1
  have haa : (a' : G) * a' = 1 := by
    have := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hAel ⟨a', haA⟩
    exact congrArg Subtype.val this
  have ha1 : (a' : G) ≠ 1 := by
    intro h
    have h1' : (QuotientGroup.mk a' : Mbar M) = 1 := by
      have : a' = 1 := Subtype.ext h
      rw [this, QuotientGroup.mk_one]
    rw [hae'] at h1'
    apply hvb1
    have := congrArg (fun z => (g : Mbar M)⁻¹ * z * (g : Mbar M)) h1'
    simpa [mul_assoc] using this
  have ha2 : orderOf (a' : G) = 2 := by
    refine orderOf_eq_prime ?_ ha1
    rw [sq, haa]
  have hc : IsConj (QuotientGroup.mk (⟨v, hvM⟩ : ↥M) : Mbar M)
      (QuotientGroup.mk (⟨(a' : G), a'.2⟩ : ↥M)) := by
    rw [isConj_iff]
    refine ⟨(g : Mbar M), ?_⟩
    rw [← hvb, ← hae']
  obtain ⟨m, hmM, hm⟩ := exists_conj_of_isConj_bar hvM a'.2 hv2 ha2 hc
  exact ⟨a', haA, ha1, m, hmM, hm⟩

theorem centralizer_le_M (hInv : PuL5InvE8) {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H)
    (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hL5 : PuL5 ↥(barIn M H)) (hP : Prop151For A M)
    {v : G} (hvM : v ∈ M) (hv2 : orderOf v = 2) : centralizer ({v} : Set G) ≤ M := by
  obtain ⟨a, haA, ha1, m, hmM, rfl⟩ := exists_conj_A hInv hs h1 h3 hk1 hL5 hvM hv2
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hga : m * g * m⁻¹ ∈ centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * g * m⁻¹ * a = m * (g * (m⁻¹ * a * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * a * m) * g) * m⁻¹ := by rw [hg]
      _ = a * (m * g * m⁻¹) := by group
  have h := hP a haA ha1 hga
  have e : g = m⁻¹ * (m * g * m⁻¹) * m := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hmM) h) hmM

theorem inU0C_A {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q)
    (h1 : Stage2Concl1 x K M Q H) (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hP : Prop151For A M) :
    InU0C M A := by
  have hAM : A ≤ M := ((A_le_K hs hk1).trans h1.H_min.1).trans h1.H_min.2.1.1
  refine inU0C_of_four_subgroups hAM hs.src.2.1 hs.src.2.2.1 fun D hDA hD4 => ?_
  have hne : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hcon
    rw [hbot, Subgroup.card_bot] at hD4
    omega
  obtain ⟨d, hdD, hd1⟩ := hne
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD)).trans (hP d (hDA hdD) hd1)

theorem controlsFusion (hInv : PuL5InvE8) {x : G} {K A M P Q H : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H) (h3 : Stage3A x A M H)
    (hk1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) (hL5 : PuL5 ↥(barIn M H)) (hP : Prop151For A M)
    (h2C : Stage2Concl2C M) {y : G} (hyM : y ∈ M) (hy2 : orderOf y = 2) :
    ControlsFusionElt M y := by
  intro g hg
  have hy₁2 : orderOf (g⁻¹ * y * g) = 2 := orderOf_conj_two hy2
  obtain ⟨a, haA, -, m, hmM, hma⟩ := exists_conj_A hInv hs h1 h3 hk1 hL5 hg hy₁2
  have hB : InU0C M (conjugate A m) := inU0C_conj (inU0C_A hs h1 hk1 hP) hmM
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hs.src.2.1
  have hBy : ∀ b ∈ conjugate A m, b * (g⁻¹ * y * g) = (g⁻¹ * y * g) * b := by
    intro b hb
    have hb' : m * b * m⁻¹ ∈ A := T4Basic.mem_conjugate_iff.1 hb
    have hcomm : (m * b * m⁻¹) * a = a * (m * b * m⁻¹) :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨_, hb'⟩ ⟨a, haA⟩)
    rw [← hma]
    calc b * (m⁻¹ * a * m) = m⁻¹ * ((m * b * m⁻¹) * a) * m := by group
      _ = m⁻¹ * (a * (m * b * m⁻¹)) * m := by rw [hcomm]
      _ = (m⁻¹ * a * m) * b := by group
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 ↥(centralizer ({y} : Set G))) := inferInstance
  have hS : IsSylowOf 2 ((Sy : Subgroup ↥(centralizer ({y} : Set G))).map
      (centralizer ({y} : Set G)).subtype) (centralizer ({y} : Set G)) := ⟨Sy, rfl⟩
  have hSM : (Sy : Subgroup ↥(centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans (centralizer_le_M hInv hs h1 h3 hk1 hL5 hP hyM hy2)
  obtain ⟨m', hm'M, hm'⟩ := prop92C h2C ⟨g, by group⟩ hB hBy hS hSM
  refine ⟨m', hm'M, ?_⟩
  calc m'⁻¹ * y * m' = m'⁻¹ * (m' * (g⁻¹ * y * g) * m'⁻¹) * m' := by rw [hm']
    _ = g⁻¹ * y * g := by group

theorem stage2Thm4_of_leaves
    (hB3 : ∀ (G : Type) [Group G] [Finite G] (x : G) (K A M P Q H : Subgroup G), Stage2Setup G x K A
        M P Q → Stage2Concl1 x K M Q H → Stage3A x A M H → PuL5 ↥(barIn M H) → QShape3 (↥K ⧸
        pPrimeCore 2 ↥K) → False) (hInv : PuL5InvE8) (h151 : S1Prop151)
    (hPU : PumpupTableU) (hO : OutG2Comm) (hB : B_B2_g4) (h2C : Stage2Thm2C) : Stage2Thm4 := by
  intro G _ _ x K A M P Q H hs h1 _ h3 hL
  obtain ⟨hk1, hL5, hxM, -⟩ := T4ElimAssembly.shape1_of_lie_of_B3a hB3 hPU hO hB hs h1 h3 hL
  have h2C' : Stage2Concl2C M := h2C G x K A M P Q H hs (Stage2Concl1.toCore h1)
  have hP : Prop151For A M := h151 G x K A M P Q H hs h1 h3 hk1 hL5
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hJ2 : ∀ v ∈ M, orderOf v = 2 → InJ2M M v := fun v hv hv2 =>
    ⟨hv, hv2, centralizer_le_M hInv hs h1 h3 hk1 hL5 hP hv hv2⟩
  have hF : ∀ v ∈ M, orderOf v = 2 → ControlsFusionElt M v := fun v hv hv2 =>
    controlsFusion hInv hs h1 h3 hk1 hL5 hP h2C' hv hv2
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  refine ⟨{y : G | IsConj x y}, lemma172 h1.preuniq.1 (hJ2 x hxM hx2) (hF x hxM hx2) ?_⟩
  intro m hmM hcomm hne
  set u := x * (m⁻¹ * x * m) with hu
  have huM : u ∈ M := M.mul_mem hxM (M.mul_mem (M.mul_mem (M.inv_mem hmM) hxM) hmM)
  have hyy : (m⁻¹ * x * m) * (m⁻¹ * x * m) = 1 := by
    calc (m⁻¹ * x * m) * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m := by group
      _ = 1 := by rw [hxx]; group
  have hu2 : orderOf u = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, hu]
      calc x * (m⁻¹ * x * m) * (x * (m⁻¹ * x * m)) = x * ((m⁻¹ * x * m) * x) * (m⁻¹ * x * m) := by group
        _ = x * (x * (m⁻¹ * x * m)) * (m⁻¹ * x * m) := by rw [← hcomm]
        _ = (x * x) * ((m⁻¹ * x * m) * (m⁻¹ * x * m)) := by group
        _ = 1 := by rw [hxx, hyy, one_mul]
    · intro h1'
      apply hne
      have : m⁻¹ * x * m = x⁻¹ := eq_inv_of_mul_eq_one_right h1'
      rw [this, inv_eq_of_mul_eq_one_right hxx]
  exact ⟨hJ2 u huM hu2, hF u huM hu2⟩

end Group

end T4S1

end CFSG.GH74.Generic.BProg.B2.T4
