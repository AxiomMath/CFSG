module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims11x

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1113

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HallHigman (IsPSolvable)

section Comp

variable {Y : Type} [Group Y] [Finite Y]

theorem comp_le_layer (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : c ≤ GLAPLayer 3 (⊤ : Subgroup Y) := by
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.l28b_glaPLayer_top_eq_layer Nat.prime_three hO]
  exact CFSG.ComponentClassification.Layer.component_le hc

theorem layer_le_of (hO : GLAPPrimeCore 3 Y = ⊥) {H : Subgroup Y}
    (h : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c ≤ H) :
    GLAPLayer 3 (⊤ : Subgroup Y) ≤ H := by
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.l28b_glaPLayer_top_eq_layer Nat.prime_three hO,
    CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  exact sSup_le fun c hc => h c hc

theorem comm_of_ne {c c' : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hc' : IsComponentOf c' (⊤ : Subgroup Y)) (hne : c ≠ c') {u v : Y} (hu : u ∈ c)
    (hv : v ∈ c') : u * v = v * u := by
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne c c' hc hc' hne)
  exact (Subgroup.mem_centralizer_iff.mp (h hu) v hv).symm

theorem isComp_conj {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y)) (g : Y) :
    IsComponentOf (GLBConj g c) (⊤ : Subgroup Y) :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) c).mpr hc

theorem three_dvd_card (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : 3 ∣ Nat.card c := by
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card c) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  have htop : GLAPPrimeCore 3 ↥c = ⊤ := by
    apply top_unique
    exact le_sSup (s := {N : Subgroup ↥c | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
      ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have hle : GLAPPrimeCoreOf 3 c ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hc.2.1
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.l28b_gLAPPrimeCoreOf_top_eq_bot hO] at hle
  have hcb : c ≤ ⊥ := by
    have hc' : GLAPPrimeCoreOf 3 c = c := by
      unfold GLAPPrimeCoreOf
      rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hc']
    exact hle
  haveI : Nontrivial ↥c := CFSG.ComponentClassification.Quasisimple.nontrivial hc.2.2
  obtain ⟨w, hw⟩ := exists_ne (1 : ↥c)
  exact hw (Subtype.ext (Subgroup.mem_bot.1 (hcb w.2)))

theorem eq_one_of_forall_comp (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥) {g : Y}
    (hg : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → ∀ u ∈ c, g * u = u * g) :
    g = 1 := by
  refine Claims11x.eq_one_of_centralizes_layer hO hO3 g fun l hl => ?_
  have hle : GLAPLayer 3 (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({g} : Set Y) :=
    layer_le_of hO fun c hc u hu => Subgroup.mem_centralizer_singleton_iff.2 (hg c hc u hu).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm

theorem eq_one_of_central (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥)
    {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y)) {u : Y} (hu : u ∈ c)
    (hcen : ∀ v ∈ c, u * v = v * u) : u = 1 := by
  refine eq_one_of_forall_comp hO hO3 fun c' hc' v hv => ?_
  by_cases h : c' = c
  · subst h
    exact hcen v hv
  · exact comm_of_ne hc hc' (fun e => h e.symm) hu hv

theorem layer_le_normalizer (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) :
    GLAPLayer 3 (⊤ : Subgroup Y) ≤ Subgroup.normalizer (c : Set Y) := by
  refine layer_le_of hO fun c' hc' => ?_
  by_cases h : c' = c
  · rw [h]
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne c' c hc' hc h)).trans
      (Subgroup.centralizer_le_normalizer _)

theorem mem_normalizer_centralizer {c : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (c : Set Y)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (c : Set Y) : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro n
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hn k hk
    have hk' : g⁻¹ * k * g ∈ c := (hg (g⁻¹ * k * g)).2 (by simpa [mul_assoc] using hk)
    have h1 := hn _ hk'
    calc k * (g * n * g⁻¹) = g * ((g⁻¹ * k * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * k := by group
  · intro hn k hk
    have hk' : g * k * g⁻¹ ∈ c := (hg k).1 hk
    have h1 := hn _ hk'
    calc k * n = g⁻¹ * ((g * k * g⁻¹) * (g * n * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * n * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
      _ = n * k := by group

theorem not_isPSolvable_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S) : ¬ IsPSolvable 3 S := by
  intro hsolv
  haveI := hS
  have hsimple : IsSimpleGroup (↥(⊤ : Subgroup S) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup S))) :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientBot).trans Subgroup.topEquiv)
  have hidx : (⊥ : Subgroup ↥(⊤ : Subgroup S)).index = Nat.card S := by
    rw [Subgroup.index_bot, Nat.card_congr Subgroup.topEquiv.toEquiv]
  rcases hsolv ⊤ (Subgroup.Normal.isSubnormal inferInstance) ⊥ hsimple with h | h
  · rw [hidx] at h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic S := isCyclic_of_prime_card (p := 3) h
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h h3

theorem not_isPSolvable_comp (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥)
    {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y)) : ¬ IsPSolvable 3 ↥c := by
  have hZ : Subgroup.center ↥c = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have h1 := eq_one_of_central hO hO3 hc w.2 fun v hv =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨v, hv⟩)).symm
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  haveI : IsSimpleGroup (↥c ⧸ Subgroup.center ↥c) := hc.2.2.2
  have hsimple : IsSimpleGroup ↥c :=
    MulEquiv.isSimpleGroup ((QuotientGroup.quotientBot.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  have hnc : ∃ a b : ↥c, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have hperf : commutator ↥c = ⊤ := hc.2.2.1
    have hbot : commutator ↥c = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hall a b
    haveI : Nontrivial ↥c := CFSG.ComponentClassification.Quasisimple.nontrivial hc.2.2
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥c)
    have : w ∈ (⊥ : Subgroup ↥c) := by rw [← hbot, hperf]; exact Subgroup.mem_top w
    exact hw (Subgroup.mem_bot.1 this)
  exact not_isPSolvable_of_simple hsimple hnc (three_dvd_card hO hc)

theorem mem_normalizer_comp (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥) {x : Y}
    (hx3 : x ^ 3 = 1) (hsolv : IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set Y)))
    {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y)) :
    x ∈ Subgroup.normalizer (c : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxN
  have hxx : x * x = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    simpa [pow_succ] using hx3
  have hc₁ := isComp_conj hc x
  have hc₂ := isComp_conj hc x⁻¹
  have h01 : c ≠ GLBConj x c := fun h => hxN (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  have h02 : c ≠ GLBConj x⁻¹ c := fun h => hxN (by
    have h1 : x⁻¹ ∈ Subgroup.normalizer (c : Set Y) := mem_normalizer_iff_gLBConj_eq.2 h.symm
    simpa using Subgroup.inv_mem _ h1)
  have h12 : GLBConj x c ≠ GLBConj x⁻¹ c := fun h => h02 (by
    have h1 := congrArg (GLBConj x) h
    rw [gLBConj_gLBConj, gLBConj_gLBConj, hxx, inv_mul_cancel, gLBConj_one] at h1
    exact h1.symm)
  have m1 : ∀ u ∈ c, x⁻¹ * u * x ∈ GLBConj x c := fun u hu =>
    mem_gLBConj.2 (by simpa [mul_assoc] using hu)
  have m2 : ∀ u ∈ c, x * u * x⁻¹ ∈ GLBConj x⁻¹ c := fun u hu =>
    mem_gLBConj.2 (by simpa [mul_assoc] using hu)
  let φ : ↥c →* Y :=
    { toFun := fun u => (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)
      map_one' := by simp
      map_mul' := by
        intro u v
        have hba1 := comm_of_ne hc hc₁ h01 v.2 (m1 u u.2)
        have hba2 := comm_of_ne hc hc₂ h02 v.2 (m2 u u.2)
        have hb1a2 := comm_of_ne hc₁ hc₂ h12 (m1 v v.2) (m2 u u.2)
        simp only [Subgroup.coe_mul]
        have e1 : x⁻¹ * ((u : Y) * v) * x = (x⁻¹ * u * x) * (x⁻¹ * v * x) := by group
        have e2 : x * ((u : Y) * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
        rw [e1, e2]
        generalize x⁻¹ * (u : Y) * x = a₁ at *
        generalize x * (u : Y) * x⁻¹ = a₂ at *
        generalize x⁻¹ * (v : Y) * x = b₁ at *
        generalize x * (v : Y) * x⁻¹ = b₂ at *
        calc (u : Y) * v * (a₁ * b₁) * (a₂ * b₂) = u * (v * a₁) * b₁ * a₂ * b₂ := by group
          _ = u * (a₁ * v) * b₁ * a₂ * b₂ := by rw [hba1]
          _ = u * a₁ * (v * (b₁ * a₂)) * b₂ := by group
          _ = u * a₁ * (v * (a₂ * b₁)) * b₂ := by rw [hb1a2]
          _ = u * a₁ * ((v * a₂) * b₁) * b₂ := by group
          _ = u * a₁ * ((a₂ * v) * b₁) * b₂ := by rw [hba2]
          _ = u * a₁ * a₂ * (v * b₁ * b₂) := by group }
  have hφ : ∀ u : ↥c, φ u = (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) := fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    rw [hφ] at hu
    have hu' : (u : Y) = (x * u * x⁻¹)⁻¹ * (x⁻¹ * u * x)⁻¹ := by
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← mul_assoc, hu]
    apply Subtype.ext
    refine eq_one_of_central hO hO3 hc u.2 fun v hv => ?_
    have h1 := comm_of_ne hc hc₁ h01 hv (Subgroup.inv_mem _ (m1 u u.2))
    have h2 := comm_of_ne hc hc₂ h02 hv (Subgroup.inv_mem _ (m2 u u.2))
    rw [hu']
    calc (x * ↑u * x⁻¹)⁻¹ * (x⁻¹ * ↑u * x)⁻¹ * v
        = (x * ↑u * x⁻¹)⁻¹ * ((x⁻¹ * ↑u * x)⁻¹ * v) := mul_assoc _ _ _
      _ = (x * ↑u * x⁻¹)⁻¹ * (v * (x⁻¹ * ↑u * x)⁻¹) := by rw [← h1]
      _ = ((x * ↑u * x⁻¹)⁻¹ * v) * (x⁻¹ * ↑u * x)⁻¹ := (mul_assoc _ _ _).symm
      _ = (v * (x * ↑u * x⁻¹)⁻¹) * (x⁻¹ * ↑u * x)⁻¹ := by rw [← h2]
      _ = v * ((x * ↑u * x⁻¹)⁻¹ * (x⁻¹ * ↑u * x)⁻¹) := mul_assoc _ _ _
  have hrange : φ.range ≤ Subgroup.centralizer ({x} : Set Y) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ]
    have ha2u := comm_of_ne hc hc₂ h02 u.2 (m2 u u.2)
    have ha1a2 := comm_of_ne hc₁ hc₂ h12 (m1 u u.2) (m2 u u.2)
    have hconj : x * (x * u * x⁻¹) * x⁻¹ = x⁻¹ * u * x := by
      calc x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
        _ = x⁻¹ * u * x := by rw [hxx, inv_inv]
    have key : x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹ =
        (x * u * x⁻¹) * u * (x⁻¹ * u * x) := by
      calc x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹
          = (x * u * x⁻¹) * u * (x * (x * u * x⁻¹) * x⁻¹) := by group
        _ = (x * u * x⁻¹) * u * (x⁻¹ * u * x) := by rw [hconj]
    have key2 : (x * u * x⁻¹) * (u : Y) * (x⁻¹ * u * x) =
        (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) := by
      generalize x * (u : Y) * x⁻¹ = a₂ at ha2u ha1a2 ⊢
      generalize x⁻¹ * (u : Y) * x = a₁ at ha2u ha1a2 ⊢
      calc a₂ * u * a₁ = (u * a₂) * a₁ := by rw [ha2u]
        _ = u * (a₂ * a₁) := mul_assoc _ _ _
        _ = u * (a₁ * a₂) := by rw [ha1a2]
        _ = u * a₁ * a₂ := (mul_assoc _ _ _).symm
    calc (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) * x
        = (x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹) * x := by
          rw [key, key2]
      _ = x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) := by group
  have h1 : IsPSolvable 3 ↥φ.range :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsolv hrange
  exact not_isPSolvable_comp hO hO3 hc
    (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (MonoidHom.ofInjective hinj).symm h1)

theorem exists_decomp (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) {z : Y} (hz : z ∈ GLAPLayer 3 (⊤ : Subgroup Y)) :
    ∃ u ∈ c, ∃ n ∈ Subgroup.centralizer (c : Set Y), u * n = z := by
  have hle : GLAPLayer 3 (⊤ : Subgroup Y) ≤ c ⊔ Subgroup.centralizer (c : Set Y) := by
    refine layer_le_of hO fun c' hc' => ?_
    by_cases h : c' = c
    · rw [h]
      exact le_sup_left
    · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne c' c hc' hc h))
  have hN : c ≤ Subgroup.normalizer ((Subgroup.centralizer (c : Set Y) : Subgroup Y) : Set Y) :=
    fun u hu => mem_normalizer_centralizer (Subgroup.le_normalizer hu)
  exact Inputs1114.exists_mul_of_mem_sup hN (hle hz)

theorem decomp_unique (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) {u u' n n' : Y} (hu : u ∈ c) (hu' : u' ∈ c)
    (hn : n ∈ Subgroup.centralizer (c : Set Y)) (hn' : n' ∈ Subgroup.centralizer (c : Set Y))
    (h : u * n = u' * n') : u = u' := by
  have hmem : u'⁻¹ * u ∈ c := c.mul_mem (c.inv_mem hu') hu
  have heq : u'⁻¹ * u = n' * n⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * n) * n⁻¹ := by group
      _ = u'⁻¹ * (u' * n') * n⁻¹ := by rw [h]
      _ = n' * n⁻¹ := by group
  have hC : u'⁻¹ * u ∈ Subgroup.centralizer (c : Set Y) := by
    rw [heq]
    exact Subgroup.mul_mem _ hn' (Subgroup.inv_mem _ hn)
  have h1 := eq_one_of_central hO hO3 hc hmem fun v hv =>
    (Subgroup.mem_centralizer_iff.1 hC v hv).symm
  calc u = u' * (u'⁻¹ * u) := by group
    _ = u' := by rw [h1, mul_one]

end Comp

section Orbit

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_normalizer_of_le_conj {N : Subgroup Y} {g : Y} (h1 : N ≤ GLBConj g N)
    (h2 : N ≤ GLBConj g⁻¹ N) : g ∈ Subgroup.normalizer (N : Set Y) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm ?_ h1
  have h3 := gLBConj_mono g h2
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h3

theorem mem_normalizer_orbit {R c₀ : Subgroup Y} {g : Y} (hgR : g ∈ R) :
    g ∈ Subgroup.normalizer ((⨆ r ∈ R, GLBConj r c₀ : Subgroup Y) : Set Y) := by
  have key : ∀ s ∈ R, (⨆ r ∈ R, GLBConj r c₀) ≤ GLBConj s (⨆ r ∈ R, GLBConj r c₀) := by
    intro s hs
    refine iSup₂_le fun r hr => ?_
    have e : GLBConj r c₀ = GLBConj s (GLBConj (r * s⁻¹) c₀) := by
      rw [gLBConj_gLBConj, inv_mul_cancel_right]
    rw [e]
    exact gLBConj_mono s (le_iSup₂ (f := fun r (_ : r ∈ R) => GLBConj r c₀) (r * s⁻¹)
      (R.mul_mem hr (R.inv_mem hs)))
  exact mem_normalizer_of_le_conj (key g hgR) (key g⁻¹ (R.inv_mem hgR))

theorem comp_le_or_centralizes {R c₀ c : Subgroup Y} (hc₀ : IsComponentOf c₀ (⊤ : Subgroup Y))
    (hc : IsComponentOf c (⊤ : Subgroup Y)) :
    c ≤ (⨆ r ∈ R, GLBConj r c₀) ∨ ∀ y ∈ (⨆ r ∈ R, GLBConj r c₀), ∀ u ∈ c, y * u = u * y := by
  by_cases h : ∃ r ∈ R, GLBConj r c₀ = c
  · obtain ⟨r, hr, rfl⟩ := h
    exact Or.inl (le_iSup₂ (f := fun r (_ : r ∈ R) => GLBConj r c₀) r hr)
  · right
    push Not at h
    have hle : (⨆ r ∈ R, GLBConj r c₀) ≤ Subgroup.centralizer (c : Set Y) :=
      iSup₂_le fun r hr => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (isComp_conj hc₀ r) hc
          (h r hr))
    intro y hy u hu
    exact (Subgroup.mem_centralizer_iff.1 (hle hy) u hu).symm

theorem centralizes_orbit {R c₀ : Subgroup Y} {g : Y} (hg : ∀ u ∈ c₀, g * u = u * g)
    (hgR : ∀ r ∈ R, r * g = g * r) : ∀ y ∈ (⨆ r ∈ R, GLBConj r c₀), g * y = y * g := by
  have hle : (⨆ r ∈ R, GLBConj r c₀) ≤ Subgroup.centralizer ({g} : Set Y) := by
    refine iSup₂_le fun r hr y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy' : r * y * r⁻¹ ∈ c₀ := mem_gLBConj.1 hy
    have h1 := hg _ hy'
    have e : r⁻¹ * g * r = g := by
      rw [mul_assoc, ← hgR r hr]
      group
    calc y * g = y * (r⁻¹ * g * r) := by rw [e]
      _ = r⁻¹ * ((r * y * r⁻¹) * g) * r := by group
      _ = r⁻¹ * (g * (r * y * r⁻¹)) * r := by rw [h1]
      _ = (r⁻¹ * g * r) * y := by group
      _ = g * y := by rw [e]
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem eq_one_of_mem_orbit (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥)
    {R c₀ : Subgroup Y} (hc₀ : IsComponentOf c₀ (⊤ : Subgroup Y)) {g : Y}
    (hgN : g ∈ ⨆ r ∈ R, GLBConj r c₀) (hg : ∀ y ∈ (⨆ r ∈ R, GLBConj r c₀), g * y = y * g) :
    g = 1 := by
  refine eq_one_of_forall_comp hO hO3 fun c hc u hu => ?_
  rcases comp_le_or_centralizes (R := R) hc₀ hc with hle | hcen
  · exact hg u (hle hu)
  · exact hcen g hgN u hu

theorem exists_central_mem {H R N : Subgroup Y} (hR : IsSylowIn 3 H R) (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set Y)) (h3N : 3 ∣ Nat.card N) :
    ∃ z : Y, z ∈ N ∧ z ∈ R ∧ (∀ r ∈ R, r * z = z * r) ∧ z ≠ 1 ∧ z ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3N
  set x₀ : Y := (x : Y) with hx₀
  have hx₀N : x₀ ∈ N := x.2
  have hx₀3 : orderOf x₀ = 3 := by rw [hx₀, Subgroup.orderOf_coe, hx]
  have hRH : R ≤ H := hR.1
  have hp : IsPGroup 3 (Subgroup.zpowers x₀) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx₀3]
    exact ⟨1, by norm_num⟩
  obtain ⟨y, hyH, hy⟩ := Claims11x.exists_conj_le_of_isSylowIn hR
    (Subgroup.zpowers_le.2 (hNH hx₀N)) hp
  have hx₁R : y⁻¹ * x₀ * y ∈ R := hy x₀ (Subgroup.mem_zpowers x₀)
  have hx₁N : y⁻¹ * x₀ * y ∈ N := by
    have := (Subgroup.mem_normalizer_iff.1 (hHN (H.inv_mem hyH)) x₀).1 hx₀N
    simpa using this
  have hx₁1 : y⁻¹ * x₀ * y ≠ 1 := by
    intro h1
    have : x₀ = 1 := by
      have e : x₀ = y * (y⁻¹ * x₀ * y) * y⁻¹ := by group
      rw [e, h1]
      group
    rw [this, orderOf_one] at hx₀3
    norm_num at hx₀3
  have hNn : (N.subgroupOf R).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hHN (hRH g.2)) n).1 hn
    simpa using this
  have hN1 : N.subgroupOf R ≠ ⊥ := by
    intro hbot
    have hmem : (⟨y⁻¹ * x₀ * y, hx₁R⟩ : ↥R) ∈ N.subgroupOf R := Subgroup.mem_subgroupOf.2 hx₁N
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx₁1 (congrArg Subtype.val hmem)
  have hR3 : IsPGroup 3 ↥R := hR.2.1
  haveI : Group.IsNilpotent ↥R := hR3.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  set W : Subgroup ↥R := N.subgroupOf R ⊓ Subgroup.center ↥R with hW
  have hW3 : IsPGroup 3 ↥W := hR3.to_subgroup W
  have hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hZ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hW3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hWnt).ne' hk
  have h3W : 3 ∣ Nat.card ↥W := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3W
  have h3 : orderOf ((w : ↥R) : Y) = 3 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : ↥R) : Y), Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 w.2).1, (w : ↥R).2,
    fun g hg => ?_, ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 w.2).2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  · intro h1
    rw [h1, orderOf_one] at h3
    norm_num at h3
  · rw [← h3]
    exact pow_orderOf_eq_one _

theorem exists_central_mem_orbit (hO : GLAPPrimeCore 3 Y = ⊥) {R c₀ : Subgroup Y}
    (hR : IsSylowIn 3 (⊤ : Subgroup Y) R) (hc₀ : IsComponentOf c₀ (⊤ : Subgroup Y)) :
    ∃ z : Y, z ∈ (⨆ r ∈ R, GLBConj r c₀) ∧ z ∈ R ∧ (∀ r ∈ R, r * z = z * r) ∧ z ≠ 1 ∧
      z ^ 3 = 1 := by
  set N : Subgroup Y := ⨆ r ∈ R, GLBConj r c₀ with hNdef
  have hc₀N : c₀ ≤ N := by
    have h1 := le_iSup₂ (f := fun r (_ : r ∈ R) => GLBConj r c₀) 1 R.one_mem
    rwa [gLBConj_one] at h1
  have h3N : 3 ∣ Nat.card N := (three_dvd_card hO hc₀).trans (Subgroup.card_dvd_of_le hc₀N)
  have hRH : R ≤ Subgroup.normalizer (N : Set Y) := fun g hg => mem_normalizer_orbit hg
  have hRsyl : IsSylowIn 3 (Subgroup.normalizer (N : Set Y)) R :=
    ⟨hRH, hR.2.1, fun R' _ hR' hRR' => hR.2.2 R' le_top hR' hRR'⟩
  exact exists_central_mem hRsyl Subgroup.le_normalizer le_rfl h3N

theorem isSylowIn_inf {H R N : Subgroup Y} (hR : IsSylowIn 3 H R) (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set Y)) : IsSylowIn 3 N (R ⊓ N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨inf_le_right, hR.2.1.to_le inf_le_left, fun S hSN hS3 hRS => ?_⟩
  obtain ⟨y, hyH, hy⟩ := Claims11x.exists_conj_le_of_isSylowIn hR (hSN.trans hNH) hS3
  have hle : GLBConj y S ≤ R ⊓ N := by
    intro w hw
    have hw' : y * w * y⁻¹ ∈ S := mem_gLBConj.1 hw
    have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact hy _ hw'
    · have := (Subgroup.mem_normalizer_iff.1 (hHN (H.inv_mem hyH)) (y * w * y⁻¹)).1 (hSN hw')
      rw [e]
      simpa using this
  refine (Subgroup.eq_of_le_of_card_ge hRS ?_).symm
  have := Subgroup.card_le_of_le hle
  rwa [Lemma1112b.card_glbConj] at this

end Orbit

section CompZ

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_centerOf_iff {c : Subgroup Y} {u : Y} :
    u ∈ centerOf c ↔ u ∈ c ∧ ∀ k ∈ c, u * k = k * u := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, fun k hk => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨k, hk⟩)).symm
  · rintro ⟨hu, hk⟩
    refine ⟨⟨u, hu⟩, Subgroup.mem_center_iff.2 fun k => Subtype.ext (hk k k.2).symm, rfl⟩

theorem mem_normalizer_centerOf {c : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (c : Set Y)) :
    g ∈ Subgroup.normalizer ((centerOf c : Subgroup Y) : Set Y) := by
  have hg' := hg
  rw [Subgroup.mem_normalizer_iff] at hg' ⊢
  intro u
  simp only [SetLike.mem_coe, mem_centerOf_iff]
  constructor
  · rintro ⟨hu, hk⟩
    refine ⟨(hg' u).1 hu, fun k hkc => ?_⟩
    have hk' : g⁻¹ * k * g ∈ c := (hg' (g⁻¹ * k * g)).2 (by simpa [mul_assoc] using hkc)
    have h1 := hk _ hk'
    calc g * u * g⁻¹ * k = g * (u * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * u) * g⁻¹ := by rw [h1]
      _ = k * (g * u * g⁻¹) := by group
  · rintro ⟨hu, hk⟩
    refine ⟨(hg' u).2 hu, fun k hkc => ?_⟩
    have h1 := hk _ ((hg' k).1 hkc)
    calc u * k = g⁻¹ * ((g * u * g⁻¹) * (g * k * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * k * g⁻¹) * (g * u * g⁻¹)) * g := by rw [h1]
      _ = k * u := by group

theorem central_comm_all {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y)) {u : Y}
    (hu : u ∈ centerOf c) :
    ∀ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) → ∀ v ∈ c', u * v = v * u := by
  obtain ⟨hu, hcen⟩ := mem_centerOf_iff.1 hu
  intro c' hc' v hv
  by_cases h : c' = c
  · subst h
    exact hcen v hv
  · exact comm_of_ne hc hc' (fun e => h e.symm) hu hv

theorem pPrimeCore_comp (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : CFSG.pPrimeCore 3 ↥c = ⊥ := by
  have hle : GLAPPrimeCoreOf 3 c ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup Y) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 3 hc.2.1
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.l28b_gLAPPrimeCoreOf_top_eq_bot hO] at hle
  have h1 : GLAPPrimeCoreOf 3 c = ⊥ := le_bot_iff.1 hle
  unfold GLAPPrimeCoreOf at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ c.subtype_injective).1 h1

theorem three_dvd_card_quot (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : 3 ∣ Nat.card (↥c ⧸ Subgroup.center ↥c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.IsQuasisimple ↥c := ⟨⟨hc.2.2.1⟩, hc.2.2.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥c hc.2.2⟩
  exact CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_dvd_card_center_quotient_of_corefree_quasisimple
    3 hq (pPrimeCore_comp hO hc)

theorem isPSolvable_of_surjective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (h : IsPSolvable 3 A) : IsPSolvable 3 B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : IsPSolvable 3 ↥(⊤ : Subgroup A) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      Subgroup.topEquiv.symm h
  have h2 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map f h1
  rw [Subgroup.map_top_of_surjective f hf] at h2
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    Subgroup.topEquiv h2

theorem not_isPSolvable_quot (hO : GLAPPrimeCore 3 Y = ⊥) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : ¬ IsPSolvable 3 (↥c ⧸ Subgroup.center ↥c) :=
  not_isPSolvable_of_simple hc.2.2.2
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥c hc.2.2)
    (three_dvd_card_quot hO hc)

theorem mem_normalizer_comp' (hO : GLAPPrimeCore 3 Y = ⊥) {x : Y} (hx3 : x ^ 3 = 1)
    (hsolv : IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set Y))) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) : x ∈ Subgroup.normalizer (c : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxN
  have hxx : x * x = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    simpa [pow_succ] using hx3
  have hc₁ := isComp_conj hc x
  have hc₂ := isComp_conj hc x⁻¹
  have h01 : c ≠ GLBConj x c := fun h => hxN (mem_normalizer_iff_gLBConj_eq.2 h.symm)
  have h02 : c ≠ GLBConj x⁻¹ c := fun h => hxN (by
    have h1 : x⁻¹ ∈ Subgroup.normalizer (c : Set Y) := mem_normalizer_iff_gLBConj_eq.2 h.symm
    simpa using Subgroup.inv_mem _ h1)
  have h12 : GLBConj x c ≠ GLBConj x⁻¹ c := fun h => h02 (by
    have h1 := congrArg (GLBConj x) h
    rw [gLBConj_gLBConj, gLBConj_gLBConj, hxx, inv_mul_cancel, gLBConj_one] at h1
    exact h1.symm)
  have m1 : ∀ u ∈ c, x⁻¹ * u * x ∈ GLBConj x c := fun u hu =>
    mem_gLBConj.2 (by simpa [mul_assoc] using hu)
  have m2 : ∀ u ∈ c, x * u * x⁻¹ ∈ GLBConj x⁻¹ c := fun u hu =>
    mem_gLBConj.2 (by simpa [mul_assoc] using hu)
  let φ : ↥c →* Y :=
    { toFun := fun u => (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)
      map_one' := by simp
      map_mul' := by
        intro u v
        have hba1 := comm_of_ne hc hc₁ h01 v.2 (m1 u u.2)
        have hba2 := comm_of_ne hc hc₂ h02 v.2 (m2 u u.2)
        have hb1a2 := comm_of_ne hc₁ hc₂ h12 (m1 v v.2) (m2 u u.2)
        simp only [Subgroup.coe_mul]
        have e1 : x⁻¹ * ((u : Y) * v) * x = (x⁻¹ * u * x) * (x⁻¹ * v * x) := by group
        have e2 : x * ((u : Y) * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
        rw [e1, e2]
        generalize x⁻¹ * (u : Y) * x = a₁ at *
        generalize x * (u : Y) * x⁻¹ = a₂ at *
        generalize x⁻¹ * (v : Y) * x = b₁ at *
        generalize x * (v : Y) * x⁻¹ = b₂ at *
        calc (u : Y) * v * (a₁ * b₁) * (a₂ * b₂) = u * (v * a₁) * b₁ * a₂ * b₂ := by group
          _ = u * (a₁ * v) * b₁ * a₂ * b₂ := by rw [hba1]
          _ = u * a₁ * (v * (b₁ * a₂)) * b₂ := by group
          _ = u * a₁ * (v * (a₂ * b₁)) * b₂ := by rw [hb1a2]
          _ = u * a₁ * ((v * a₂) * b₁) * b₂ := by group
          _ = u * a₁ * ((a₂ * v) * b₁) * b₂ := by rw [hba2]
          _ = u * a₁ * a₂ * (v * b₁ * b₂) := by group }
  have hφ : ∀ u : ↥c, φ u = (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) := fun _ => rfl
  have hker : φ.ker ≤ Subgroup.center ↥c := by
    intro u hu
    rw [MonoidHom.mem_ker, hφ] at hu
    have hu' : (u : Y) = (x * u * x⁻¹)⁻¹ * (x⁻¹ * u * x)⁻¹ := by
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← mul_assoc, hu]
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    have h1 := comm_of_ne hc hc₁ h01 v.2 (Subgroup.inv_mem _ (m1 u u.2))
    have h2 := comm_of_ne hc hc₂ h02 v.2 (Subgroup.inv_mem _ (m2 u u.2))
    simp only [Subgroup.coe_mul]
    rw [hu']
    calc (v : Y) * ((x * ↑u * x⁻¹)⁻¹ * (x⁻¹ * ↑u * x)⁻¹)
        = ((v : Y) * (x * ↑u * x⁻¹)⁻¹) * (x⁻¹ * ↑u * x)⁻¹ := (mul_assoc _ _ _).symm
      _ = ((x * ↑u * x⁻¹)⁻¹ * v) * (x⁻¹ * ↑u * x)⁻¹ := by rw [h2]
      _ = (x * ↑u * x⁻¹)⁻¹ * ((v : Y) * (x⁻¹ * ↑u * x)⁻¹) := mul_assoc _ _ _
      _ = (x * ↑u * x⁻¹)⁻¹ * ((x⁻¹ * ↑u * x)⁻¹ * v) := by rw [h1]
      _ = (x * ↑u * x⁻¹)⁻¹ * (x⁻¹ * ↑u * x)⁻¹ * v := (mul_assoc _ _ _).symm
  have hrange : φ.range ≤ Subgroup.centralizer ({x} : Set Y) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ]
    have ha2u := comm_of_ne hc hc₂ h02 u.2 (m2 u u.2)
    have ha1a2 := comm_of_ne hc₁ hc₂ h12 (m1 u u.2) (m2 u u.2)
    have hconj : x * (x * u * x⁻¹) * x⁻¹ = x⁻¹ * u * x := by
      calc x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
        _ = x⁻¹ * u * x := by rw [hxx, inv_inv]
    have key : x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹ =
        (x * u * x⁻¹) * u * (x⁻¹ * u * x) := by
      calc x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹
          = (x * u * x⁻¹) * u * (x * (x * u * x⁻¹) * x⁻¹) := by group
        _ = (x * u * x⁻¹) * u * (x⁻¹ * u * x) := by rw [hconj]
    have key2 : (x * u * x⁻¹) * (u : Y) * (x⁻¹ * u * x) =
        (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) := by
      generalize x * (u : Y) * x⁻¹ = a₂ at ha2u ha1a2 ⊢
      generalize x⁻¹ * (u : Y) * x = a₁ at ha2u ha1a2 ⊢
      calc a₂ * u * a₁ = (u * a₂) * a₁ := by rw [ha2u]
        _ = u * (a₂ * a₁) := mul_assoc _ _ _
        _ = u * (a₁ * a₂) := by rw [ha1a2]
        _ = u * a₁ * a₂ := (mul_assoc _ _ _).symm
    calc (u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹) * x
        = (x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) * x⁻¹) * x := by
          rw [key, key2]
      _ = x * ((u : Y) * (x⁻¹ * u * x) * (x * u * x⁻¹)) := by group
  have h1 : IsPSolvable 3 ↥φ.range :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsolv hrange
  have h2 : IsPSolvable 3 (↥c ⧸ φ.ker) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange φ).symm h1
  have hle : φ.ker ≤ (Subgroup.center ↥c).comap (MonoidHom.id ↥c) := by
    rw [Subgroup.comap_id]
    exact hker
  have hsurj : Function.Surjective (QuotientGroup.map φ.ker (Subgroup.center ↥c)
      (MonoidHom.id ↥c) hle) :=
    QuotientGroup.map_surjective_of_surjective (N := φ.ker) (Subgroup.center ↥c) (MonoidHom.id ↥c)
      QuotientGroup.mk_surjective hle
  exact not_isPSolvable_quot hO hc (isPSolvable_of_surjective _ hsurj h2)

theorem exists_sylow_normalized {c : Subgroup Y} {x : Y}
    (hxc : x ∈ Subgroup.normalizer (c : Set Y)) (hx3 : x ^ 3 = 1) :
    ∃ R : Subgroup Y, IsSylowIn 3 (Subgroup.normalizer (c : Set Y)) R ∧ x ∈ R ∧
      IsSylowIn 3 c (R ⊓ c) ∧ x ∈ Subgroup.normalizer ((R ⊓ c : Subgroup Y) : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hx3)
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  obtain ⟨R, hR, hxR⟩ := Lemma1112b.exists_isSylowIn_ge (Subgroup.zpowers_le.2 hxc) hp
  have hxR' : x ∈ R := hxR (Subgroup.mem_zpowers x)
  refine ⟨R, hR, hxR', isSylowIn_inf hR Subgroup.le_normalizer le_rfl, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem hxR' (Subgroup.mem_inf.1 hw).1) (R.inv_mem hxR'),
      (Subgroup.mem_normalizer_iff.1 hxc w).1 (Subgroup.mem_inf.1 hw).2⟩
  · intro hw
    obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
    have e : w = x⁻¹ * (x * w * x⁻¹) * x := by group
    refine Subgroup.mem_inf.2 ⟨?_, (Subgroup.mem_normalizer_iff.1 hxc w).2 hw2⟩
    rw [e]
    exact R.mul_mem (R.mul_mem (R.inv_mem hxR') hw1) hxR'

end CompZ

@[expose] def InputU43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K →
    (∃ D : Subgroup G, D ≤ centerOf K ∧ IsElemAbelian 3 D ∧ Nat.card D = 9) →
      (∀ D : Subgroup G, D ≤ centerOf K → IsElemAbelian 3 D → Nat.card D ≤ 9) ∧
      (∀ g ∈ Subgroup.normalizer (K : Set G), g ^ 3 = 1 → ∀ z ∈ centerOf K, g * z = z * g) ∧
      (∀ D : Subgroup G, D ≤ centerOf K → IsElemAbelian 3 D → Nat.card D = 9 →
        ¬ ∀ z ∈ D, z ≠ 1 → ∀ w ∈ D, w ≠ 1 →
          ∃ n ∈ Subgroup.normalizer (K : Set G), n⁻¹ * z * n = w) ∧
      (∀ S : Subgroup G, IsSylowIn 3 K S → ∃ F : Subgroup G, F ≤ S ∧ IsElemAbelian 3 F ∧
        Nat.card F = 3 ^ 6 ∧
        ∀ F' : Subgroup G, F' ≤ S → IsElemAbelian 3 F' → Nat.card F' = 3 ^ 6 → F' = F)

section Central

variable {Y : Type} [Group Y] [Finite Y]

structure CentralData (Y : Type) [Group Y] [Finite Y] (V : Subgroup Y) (x : Y) : Prop where
  hO : GLAPPrimeCore 3 Y = ⊥
  hK : CFSG.Open.IsKGroup Y
  hVL : V ≤ GLAPLayer 3 (⊤ : Subgroup Y)
  hVc : ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → ∀ v ∈ V, ∀ u ∈ c, v * u = u * v
  hVel : IsElemAbelian 3 V
  hV9 : Nat.card V = 9
  hx3 : x ^ 3 = 1
  hxV : ∀ v ∈ V, x * v = v * x
  hxnV : x ∉ V
  hsolv : IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set Y))
  hrk : ∀ F : Subgroup Y, F ≤ Subgroup.centralizer ({x} : Set Y) → IsElemAbelian 3 F →
    Nat.card F < 81
  htr : ∀ z ∈ V, z ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ n : Y, n⁻¹ * z * n = w

theorem mem_zpowers_of_ne_one {x b : Y} (hx3 : x ^ 3 = 1) (hb : b ∈ Subgroup.zpowers x)
    (hb1 : b ≠ 1) : x ∈ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hb
  have hx : Nat.card (Subgroup.zpowers x) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx3
  have hb3 : Nat.card (Subgroup.zpowers b) ∣ 3 := (Subgroup.card_dvd_of_le hle).trans hx
  have hbne : Nat.card (Subgroup.zpowers b) ≠ 1 := by
    rw [Nat.card_zpowers]
    intro h1
    exact hb1 (orderOf_eq_one_iff.1 h1)
  have hb3' : Nat.card (Subgroup.zpowers b) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hb3).resolve_left hbne
  have hx3' : Nat.card (Subgroup.zpowers x) = 3 := by
    have := Subgroup.card_le_of_le hle
    have h2 := Nat.le_of_dvd (by norm_num) hx
    omega
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hb3', hx3'])
  rw [heq]
  exact Subgroup.mem_zpowers x

namespace CentralData

variable {V : Subgroup Y} {x : Y}

theorem mem_sup (D : CentralData Y V x) {u : Y} (hu3 : u ^ 3 = 1) (hux : x * u = u * x)
    (huV : ∀ v ∈ V, u * v = v * u) : ∃ v ∈ V, ∃ b ∈ Subgroup.zpowers x, u = v * b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVx : V ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Y) : Set Y) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((show Commute x v from D.hxV v hv).zpow_left k).eq
  have hx1 : x ≠ 1 := fun h => D.hxnV (h ▸ V.one_mem)
  have hxc : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime D.hx3 hx1]
  have hdisj : V ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbV, hbx⟩ := Subgroup.mem_inf.1 hb
    by_contra hb1
    exact D.hxnV ((Subgroup.zpowers_le.2 hbV) (mem_zpowers_of_ne_one D.hx3 hbx hb1))
  have hWel : IsElemAbelian 3 (V ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_of_commute D.hVel (CFSG.Open.isElemAbelian_zpowers D.hx3) hVx
  have hWcard : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup Y) = 27 := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute
      (fun v hv b hb => (Subgroup.mem_centralizer_iff.1 (hVx hv) b hb).symm) hdisj, D.hV9, hxc]
  have hWu : V ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup Y) : Set Y) := by
    refine sup_le ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((show Commute u v from huV v hv).zpow_left k).eq
    · intro b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
      exact ((show Commute u x from hux.symm).zpow_zpow j k).eq
  have hEel : IsElemAbelian 3 (V ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers u) :=
    isElemAbelian_sup_of_commute hWel (CFSG.Open.isElemAbelian_zpowers hu3) hWu
  have hEC : V ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers u ≤ Subgroup.centralizer ({x} : Set Y) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.2 (D.hxV v hv).symm
    · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hux.symm)
  have hlt := D.hrk _ hEC hEel
  have hdvd : 27 ∣ Nat.card (V ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers u : Subgroup Y) := by
    rw [← hWcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (Lemma118T.isPGroup_of_isElemAbelian hEel)
  have hk3 : k = 3 := by
    rw [hk] at hdvd hlt
    have h1 : 3 ≤ k := by
      by_contra h
      push Not at h
      have : 3 ^ k < 27 := by
        calc 3 ^ k < 3 ^ 3 := Nat.pow_lt_pow_right (by norm_num) h
          _ = 27 := by norm_num
      exact absurd (Nat.le_of_dvd (by positivity) hdvd) (by omega)
    have h2 : k < 4 := by
      by_contra h
      push Not at h
      have : 81 ≤ 3 ^ k := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    omega
  have heq : V ⊔ Subgroup.zpowers x = V ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers u :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hk, hk3, hWcard]; norm_num)
  have huW : u ∈ V ⊔ Subgroup.zpowers x := by
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  obtain ⟨v, hv, b, hb, hvb⟩ := exists_mul_of_mem_sup hVx huW
  exact ⟨v, hv, b, hb, hvb⟩

theorem centralizes_of_mem_zpowers {c' : Subgroup Y} {w : Y} (hw : ∀ u ∈ c', w * u = u * w)
    (hx : x ∈ Subgroup.zpowers w) : ∀ u ∈ c', x * u = u * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  intro u hu
  exact ((show Commute w u from hw u hu).zpow_left k).eq

theorem eq_one_or_self_or_inv {ζ w : Y} (hζ3 : ζ ^ 3 = 1) (hw : w ∈ Subgroup.zpowers ζ) :
    w = 1 ∨ w = ζ ∨ w = ζ⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hk : ζ ^ k = ζ ^ (k % 3) := by
    by_cases hζ1 : ζ = 1
    · subst hζ1
      simp
    · have hord : ((orderOf ζ : ℕ) : ℤ) = 3 := by rw [orderOf_eq_prime hζ3 hζ1]; norm_num
      rw [← zpow_mod_orderOf ζ k, hord]
  rw [hk]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases (k % 3)
  · left
    simp
  · right; left
    simp
  · right; right
    rw [eq_inv_iff_mul_eq_one]
    calc ζ ^ (2 : ℤ) * ζ = ζ ^ 3 := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
          norm_cast
      _ = 1 := hζ3

theorem comm_of_center (IU : InputU43) (D : CentralData Y V x) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) {ζ : Y} (hζ : ζ ∈ centerOf c) (hζ3 : ζ ^ 3 = 1) :
    x * ζ = ζ * x := by
  have hxN := mem_normalizer_comp' D.hO D.hx3 D.hsolv hc
  by_cases hE : ∃ E : Subgroup Y, E ≤ centerOf c ∧ IsElemAbelian 3 E ∧ Nat.card E = 9
  · exact (IU Y c hc.2.2 (D.hK.subgroup c) hE).2.1 x hxN D.hx3 ζ hζ
  · by_cases hζ1 : ζ = 1
    · rw [hζ1, mul_one, one_mul]
    set ζ' : Y := x * ζ * x⁻¹ with hζ'
    have hζ'Z : ζ' ∈ centerOf c :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centerOf hxN) ζ).1 hζ
    have hζ'3 : ζ' ^ 3 = 1 := by rw [hζ', conj_pow, hζ3]; group
    have hcomm : ζ' * ζ = ζ * ζ' :=
      (mem_centerOf_iff.1 hζ'Z).2 ζ (mem_centerOf_iff.1 hζ).1
    have hmem : ζ' ∈ Subgroup.zpowers ζ := by
      by_contra hn
      apply hE
      obtain ⟨hel, hcard⟩ := Claims11x.plane_of_commute hζ'3 hζ3 hζ1 hcomm hn
      refine ⟨_, sup_le (Subgroup.zpowers_le.2 hζ'Z) (Subgroup.zpowers_le.2 hζ), hel, hcard⟩
    rcases eq_one_or_self_or_inv hζ3 hmem with h | h | h
    · exfalso
      apply hζ1
      have : x * ζ * x⁻¹ = 1 := h
      calc ζ = x⁻¹ * (x * ζ * x⁻¹) * x := by group
        _ = 1 := by rw [this]; group
    · have : x * ζ * x⁻¹ = ζ := h
      calc x * ζ = (x * ζ * x⁻¹) * x := by group
        _ = ζ * x := by rw [this]
    · exfalso
      have h1 : x * ζ * x⁻¹ = ζ⁻¹ := h
      have hxx : x * x * x = 1 := by simpa [pow_succ] using D.hx3
      have h2 : x * ζ⁻¹ * x⁻¹ = ζ := by
        rw [show x * ζ⁻¹ * x⁻¹ = (x * ζ * x⁻¹)⁻¹ by group, h1, inv_inv]
      have h3 : (x * x * x) * ζ * (x * x * x)⁻¹ = ζ⁻¹ := by
        calc (x * x * x) * ζ * (x * x * x)⁻¹ = x * (x * (x * ζ * x⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = ζ⁻¹ := by rw [h1, h2, h1]
      rw [hxx] at h3
      simp only [one_mul, inv_one, mul_one] at h3
      apply hζ1
      have h4 : ζ * ζ = 1 := by
        calc ζ * ζ = ζ * ζ⁻¹ := by rw [← h3]
          _ = 1 := mul_inv_cancel ζ
      calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by group
        _ = 1 := by rw [hζ3, h4]; group

theorem false_of_relation (D : CentralData Y V x) {c₀ : Subgroup Y}
    (hc₀ : IsComponentOf c₀ (⊤ : Subgroup Y)) {y₀ z₀ w : Y} (hy₀ : y₀ ∈ c₀) (hy₀3 : y₀ ^ 3 = 1)
    (hy₀nc : ∃ g ∈ c₀, y₀ * g ≠ g * y₀) (hz₀V : z₀ ∈ V) (hz₀1 : z₀ ≠ 1)
    (hdef₀ : x * y₀ * x⁻¹ = y₀ * z₀) (hw3 : w ^ 3 = 1) (hwc : ∀ g ∈ c₀, w * g = g * w)
    (hwV : ∀ v ∈ V, w * v = v * w) (hdefw : x * w * x⁻¹ = w * z₀) : False := by
  have hwy : w * y₀ = y₀ * w := hwc y₀ hy₀
  set y : Y := w * y₀⁻¹ with hy
  have hxy : x * y * x⁻¹ = y := by
    calc x * y * x⁻¹ = (x * w * x⁻¹) * (x * y₀ * x⁻¹)⁻¹ := by rw [hy]; group
      _ = (w * z₀) * (y₀ * z₀)⁻¹ := by rw [hdefw, hdef₀]
      _ = w * y₀⁻¹ := by group
  have hxy' : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hxy]
  have hy3 : y ^ 3 = 1 := by
    have hc : Commute w y₀⁻¹ := by
      show w * y₀⁻¹ = y₀⁻¹ * w
      calc w * y₀⁻¹ = y₀⁻¹ * (y₀ * w) * y₀⁻¹ := by group
        _ = y₀⁻¹ * (w * y₀) * y₀⁻¹ := by rw [hwy]
        _ = y₀⁻¹ * w := by group
    rw [hy, hc.mul_pow, hw3, inv_pow, hy₀3]
    group
  have hyV : ∀ v ∈ V, y * v = v * y := by
    intro v hv
    have h1 := hwV v hv
    have h2 : y₀⁻¹ * v = v * y₀⁻¹ := by
      have h3 : v * y₀ = y₀ * v := D.hVc c₀ hc₀ v hv y₀ hy₀
      calc y₀⁻¹ * v = y₀⁻¹ * (v * y₀) * y₀⁻¹ := by group
        _ = y₀⁻¹ * (y₀ * v) * y₀⁻¹ := by rw [h3]
        _ = v * y₀⁻¹ := by group
    calc y * v = w * (y₀⁻¹ * v) := by rw [hy]; group
      _ = w * (v * y₀⁻¹) := by rw [h2]
      _ = (w * v) * y₀⁻¹ := (mul_assoc _ _ _).symm
      _ = (v * w) * y₀⁻¹ := by rw [h1]
      _ = v * y := by rw [hy]; group
  obtain ⟨v, hv, b, hb, hvb⟩ := D.mem_sup hy3 hxy' hyV
  by_cases hb1 : b = 1
  · rw [hb1, mul_one] at hvb
    obtain ⟨g, hgc, hyg⟩ := hy₀nc
    apply hyg
    have h1 : y * g = g * y := by rw [hvb]; exact D.hVc c₀ hc₀ v hv g hgc
    have h2 := hwc g hgc
    have e : y₀ = y⁻¹ * w := by rw [hy]; group
    rw [e]
    calc y⁻¹ * w * g = y⁻¹ * (w * g) := mul_assoc _ _ _
      _ = y⁻¹ * (g * w) := by rw [h2]
      _ = (y⁻¹ * g) * w := (mul_assoc _ _ _).symm
      _ = (g * y⁻¹) * w := by
          rw [show y⁻¹ * g = g * y⁻¹ by
            calc y⁻¹ * g = y⁻¹ * (g * y) * y⁻¹ := by group
              _ = y⁻¹ * (y * g) * y⁻¹ := by rw [h1]
              _ = g * y⁻¹ := by group]
      _ = g * (y⁻¹ * w) := mul_assoc _ _ _
  · have hxb := mem_zpowers_of_ne_one D.hx3 hb hb1
    have hbe : b = v⁻¹ * y := by rw [hvb]; group
    have hby₀ : b * y₀ = y₀ * b := by
      have h1 : v * y₀ = y₀ * v := D.hVc c₀ hc₀ v hv y₀ hy₀
      have h2 : y * y₀ = y₀ * y := by
        rw [hy]
        calc w * y₀⁻¹ * y₀ = w := by group
          _ = y₀ * (y₀⁻¹ * w) := by group
          _ = y₀ * (w * y₀⁻¹) := by
              rw [show y₀⁻¹ * w = w * y₀⁻¹ by
                calc y₀⁻¹ * w = y₀⁻¹ * (w * y₀) * y₀⁻¹ := by group
                  _ = y₀⁻¹ * (y₀ * w) * y₀⁻¹ := by rw [hwy]
                  _ = w * y₀⁻¹ := by group]
      rw [hbe]
      calc v⁻¹ * y * y₀ = v⁻¹ * (y * y₀) := mul_assoc _ _ _
        _ = v⁻¹ * (y₀ * y) := by rw [h2]
        _ = (v⁻¹ * y₀) * y := (mul_assoc _ _ _).symm
        _ = (y₀ * v⁻¹) * y := by
            rw [show v⁻¹ * y₀ = y₀ * v⁻¹ by
              calc v⁻¹ * y₀ = v⁻¹ * (y₀ * v) * v⁻¹ := by group
                _ = v⁻¹ * (v * y₀) * v⁻¹ := by rw [h1]
                _ = y₀ * v⁻¹ := by group]
        _ = y₀ * (v⁻¹ * y) := mul_assoc _ _ _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxb
    have hxy₀ : x * y₀ = y₀ * x := by
      rw [← hk]
      exact ((show Commute b y₀ from hby₀).zpow_left k).eq
    apply hz₀1
    have h1 : x * y₀ * x⁻¹ = y₀ := by rw [hxy₀]; group
    rw [h1] at hdef₀
    calc z₀ = y₀⁻¹ * (y₀ * z₀) := by group
      _ = 1 := by rw [← hdef₀]; group

end CentralData

end Central

section FixedPoints

variable {Y : Type} [Group Y] [Finite Y]

theorem card_ker_comp_le {A : Type} [Group A] [Finite A] (α β : A →* A) :
    Nat.card (β.comp α).ker ≤ Nat.card β.ker * Nat.card α.ker := by
  set K := (β.comp α).ker with hK
  have hmem : ∀ k : ↥K, α k ∈ β.ker := fun k => by
    have := k.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at this
    exact MonoidHom.mem_ker.2 this
  let α' : ↥K →* ↥β.ker := (α.comp K.subtype).codRestrict β.ker (fun k => hmem k)
  have h1 : Nat.card ↥K = Nat.card ↥α'.range * Nat.card ↥α'.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α'.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α').toEquiv]
  have h2 : Nat.card ↥α'.range ≤ Nat.card ↥β.ker := Subgroup.card_le_card_group _
  have h3 : Nat.card ↥α'.ker ≤ Nat.card ↥α.ker := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥K) : A), ?_⟩) ?_
    · have h := MonoidHom.mem_ker.1 k.2
      have h' := congrArg Subtype.val h
      exact MonoidHom.mem_ker.2 h'
    · intro p q hpq
      simp only [Subtype.mk.injEq] at hpq
      exact Subtype.ext (Subtype.ext hpq)
  rw [h1]
  exact Nat.mul_le_mul h2 h3

theorem cube_identity {a b c : Y} (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) : c⁻¹ * b * a⁻¹ * b * c⁻¹ * b * c⁻¹ * a = 1 := by
  have hX : Commute a (b * c⁻¹ * b * c⁻¹) :=
    ((hab.mul_right hac.inv_right).mul_right hab).mul_right hac.inv_right
  have hbc' : Commute b c⁻¹ := hbc.inv_right
  have e1 : c⁻¹ * b * a⁻¹ * b * c⁻¹ * b * c⁻¹ * a = c⁻¹ * b * (a⁻¹ * (b * c⁻¹ * b * c⁻¹) * a) := by
    group
  have e2 : a⁻¹ * (b * c⁻¹ * b * c⁻¹) * a = b * c⁻¹ * b * c⁻¹ := by
    rw [mul_assoc, ← hX.eq]
    group
  rw [e1, e2]
  have e3 : c⁻¹ * b = b * c⁻¹ := hbc'.eq.symm
  calc c⁻¹ * b * (b * c⁻¹ * b * c⁻¹) = (c⁻¹ * b) * (b * c⁻¹) * (b * c⁻¹) := by group
    _ = (b * c⁻¹) * (b * c⁻¹) * (b * c⁻¹) := by rw [e3]
    _ = (b * c⁻¹) ^ 3 := (pow_three' _).symm
    _ = b ^ 3 * c⁻¹ ^ 3 := hbc'.mul_pow 3
    _ = 1 := by rw [hb3, inv_pow, hc3]; group

theorem card_le_cube_fixed {F : Subgroup Y} (hF : IsElemAbelian 3 F) {x : Y}
    (hxF : x ∈ Subgroup.normalizer (F : Set Y)) (hx3 : x ^ 3 = 1) :
    Nat.card F ≤ Nat.card ↥(F ⊓ Subgroup.centralizer ({x} : Set Y)) ^ 3 := by
  have hconj : ∀ f ∈ F, x * f * x⁻¹ ∈ F := fun f hf => (Subgroup.mem_normalizer_iff.1 hxF f).1 hf
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb => hF.comm ha hb
  let φ : ↥F →* ↥F :=
    { toFun := fun f => ⟨(f : Y)⁻¹ * (x * f * x⁻¹), F.mul_mem (F.inv_mem f.2) (hconj f f.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro f g
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have h1 := hcomm _ (F.inv_mem g.2) _ (F.mul_mem (F.inv_mem f.2) (hconj f f.2))
        calc ((f : Y) * g)⁻¹ * (x * (f * g) * x⁻¹)
            = (g : Y)⁻¹ * ((f : Y)⁻¹ * (x * f * x⁻¹)) * (x * g * x⁻¹) := by group
          _ = ((f : Y)⁻¹ * (x * f * x⁻¹)) * (g : Y)⁻¹ * (x * g * x⁻¹) := by rw [h1]
          _ = (f : Y)⁻¹ * (x * f * x⁻¹) * ((g : Y)⁻¹ * (x * g * x⁻¹)) := by group }
  have hφ : ∀ f : ↥F, (φ f : Y) = (f : Y)⁻¹ * (x * f * x⁻¹) := fun _ => rfl
  have hxxx : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hφ3 : ∀ f : ↥F, φ (φ (φ f)) = 1 := by
    intro f
    apply Subtype.ext
    have haF : (f : Y) ∈ F := f.2
    have hbF : x * (f : Y) * x⁻¹ ∈ F := hconj _ haF
    have hcF : x * (x * (f : Y) * x⁻¹) * x⁻¹ ∈ F := hconj _ hbF
    have hd : x * (x * (x * (f : Y) * x⁻¹) * x⁻¹) * x⁻¹ = f := by
      calc x * (x * (x * (f : Y) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * f * (x * x * x)⁻¹ := by group
        _ = f := by rw [hxxx]; group
    have e : (φ (φ (φ f)) : Y) = (x * (x * (f : Y) * x⁻¹) * x⁻¹)⁻¹ * (x * f * x⁻¹) * (f : Y)⁻¹ *
        (x * f * x⁻¹) * (x * (x * (f : Y) * x⁻¹) * x⁻¹)⁻¹ * (x * f * x⁻¹) *
        (x * (x * (f : Y) * x⁻¹) * x⁻¹)⁻¹ * (x * (x * (x * (f : Y) * x⁻¹) * x⁻¹) * x⁻¹) := by
      simp only [hφ]
      group
    rw [e, hd]
    simp only [Subgroup.coe_one]
    exact cube_identity (hcomm _ haF _ hbF) (hcomm _ haF _ hcF) (hcomm _ hbF _ hcF)
      (hF.2 _ hbF) (hF.2 _ hcF)
  have hker : Nat.card φ.ker = Nat.card ↥(F ⊓ Subgroup.centralizer ({x} : Set Y)) := by
    have heq : φ.ker = (F ⊓ Subgroup.centralizer ({x} : Set Y)).subgroupOf F := by
      ext f
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h1 := congrArg Subtype.val h
        rw [hφ, Subgroup.coe_one, inv_mul_eq_one] at h1
        refine ⟨f.2, ?_⟩
        calc (f : Y) * x = (x * f * x⁻¹) * x := by rw [← h1]
          _ = x * f := by group
      · rintro ⟨-, h⟩
        apply Subtype.ext
        rw [hφ, Subgroup.coe_one, inv_mul_eq_one]
        calc (f : Y) = (f : Y) * x * x⁻¹ := by group
          _ = x * f * x⁻¹ := by rw [h]
    rw [heq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have htop : (φ.comp (φ.comp φ)).ker = ⊤ := by
    rw [eq_top_iff]
    intro f _
    exact MonoidHom.mem_ker.2 (hφ3 f)
  have h1 := card_ker_comp_le (φ.comp φ) φ
  have h2 := card_ker_comp_le φ φ
  rw [htop, Subgroup.card_top] at h1
  rw [← hker]
  calc Nat.card ↥F ≤ Nat.card φ.ker * Nat.card (φ.comp φ).ker := h1
    _ ≤ Nat.card φ.ker * (Nat.card φ.ker * Nat.card φ.ker) := Nat.mul_le_mul_left _ h2
    _ = Nat.card φ.ker ^ 3 := by ring

theorem card_mul_le_card_sup_mul_inf {F₁ F₂ : Subgroup Y}
    (hc : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a) :
    Nat.card F₁ * Nat.card F₂ ≤ Nat.card (F₁ ⊔ F₂ : Subgroup Y) * Nat.card (F₁ ⊓ F₂ : Subgroup Y) := by
  let μ : ↥F₁ × ↥F₂ →* Y := MonoidHom.noncommCoprod F₁.subtype F₂.subtype (fun a b => hc a a.2 b b.2)
  have hμ : ∀ ab : ↥F₁ × ↥F₂, μ ab = (ab.1 : Y) * ab.2 := fun _ => rfl
  have hrange : μ.range ≤ F₁ ⊔ F₂ := by
    rintro _ ⟨ab, rfl⟩
    rw [hμ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ab.1.2) (Subgroup.mem_sup_right ab.2.2)
  have hker : Nat.card μ.ker ≤ Nat.card (F₁ ⊓ F₂ : Subgroup Y) := by
    have hmem : ∀ ab : ↥μ.ker, ((ab : ↥F₁ × ↥F₂).1 : Y) ∈ F₁ ⊓ F₂ := by
      intro ab
      have h1 : ((ab : ↥F₁ × ↥F₂).1 : Y) * (ab : ↥F₁ × ↥F₂).2 = 1 := by
        rw [← hμ]
        exact MonoidHom.mem_ker.1 ab.2
      have h2 : ((ab : ↥F₁ × ↥F₂).1 : Y) = ((ab : ↥F₁ × ↥F₂).2 : Y)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      refine Subgroup.mem_inf.2 ⟨(ab : ↥F₁ × ↥F₂).1.2, ?_⟩
      rw [h2]
      exact F₂.inv_mem (ab : ↥F₁ × ↥F₂).2.2
    refine Nat.card_le_card_of_injective (fun ab => ⟨_, hmem ab⟩) ?_
    intro p q hpq
    simp only [Subtype.mk.injEq] at hpq
    have h1 : ((p : ↥F₁ × ↥F₂).1 : Y) = ((q : ↥F₁ × ↥F₂).1 : Y) := hpq
    have hp : ((p : ↥F₁ × ↥F₂).1 : Y) * (p : ↥F₁ × ↥F₂).2 = 1 := by
      rw [← hμ]; exact MonoidHom.mem_ker.1 p.2
    have hq : ((q : ↥F₁ × ↥F₂).1 : Y) * (q : ↥F₁ × ↥F₂).2 = 1 := by
      rw [← hμ]; exact MonoidHom.mem_ker.1 q.2
    have h2 : ((p : ↥F₁ × ↥F₂).2 : Y) = ((q : ↥F₁ × ↥F₂).2 : Y) := by
      rw [eq_inv_of_mul_eq_one_right hp, eq_inv_of_mul_eq_one_right hq, h1]
    apply Subtype.ext
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hcard : Nat.card (↥F₁ × ↥F₂) = Nat.card μ.range * Nat.card μ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup μ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv]
  rw [Nat.card_prod] at hcard
  rw [hcard]
  exact Nat.mul_le_mul (Subgroup.card_le_of_le hrange) hker

end FixedPoints

section CentralCases

variable {Y : Type} [Group Y] [Finite Y]

namespace CentralData

variable {V : Subgroup Y} {x : Y}

theorem le_centerOf (D : CentralData Y V x) {c : Subgroup Y} (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hVc : V ≤ c) : V ≤ centerOf c := fun v hv =>
  mem_centerOf_iff.2 ⟨hVc hv, fun k hk => D.hVc c hc v hv k hk⟩

theorem exists_E6 (IU : InputU43) (D : CentralData Y V x) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y)) (hVc : V ≤ c) :
    ∃ F : Subgroup Y, F ≤ c ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 6 ∧
      x ∈ Subgroup.normalizer (F : Set Y) := by
  have hxN := mem_normalizer_comp' D.hO D.hx3 D.hsolv hc
  obtain ⟨R, -, -, hS, hxS⟩ := exists_sylow_normalized hxN D.hx3
  obtain ⟨-, -, -, h4⟩ := IU Y c hc.2.2 (D.hK.subgroup c) ⟨V, D.le_centerOf hc hVc, D.hVel, D.hV9⟩
  obtain ⟨F, hFS, hFel, hFcard, huniq⟩ := h4 _ hS
  refine ⟨F, hFS.trans inf_le_right, hFel, hFcard, ?_⟩
  have h1 : GLBConj x⁻¹ F = F := by
    refine huniq _ ?_ (Lemma118T.isElemAbelian_gLBConj' hFel x⁻¹) (by rw [Lemma1112b.card_glbConj, hFcard])
    intro w hw
    have hw' : x⁻¹ * w * x⁻¹⁻¹ ∈ F := mem_gLBConj.1 hw
    have e : w = x * (x⁻¹ * w * x⁻¹⁻¹) * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hxS _).1 (hFS hw')
  have h2 : x⁻¹ ∈ Subgroup.normalizer (F : Set Y) := mem_normalizer_iff_gLBConj_eq.2 h1
  simpa using Subgroup.inv_mem _ h2

theorem false_of_two (IU : InputU43) (D : CentralData Y V x) {c₁ c₂ : Subgroup Y}
    (hc₁ : IsComponentOf c₁ (⊤ : Subgroup Y)) (hc₂ : IsComponentOf c₂ (⊤ : Subgroup Y))
    (hne : c₁ ≠ c₂) (hV1 : V ≤ c₁) (hV2 : V ≤ c₂) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F₁, hF₁c, hF₁el, hF₁card, hxF₁⟩ := D.exists_E6 IU hc₁ hV1
  obtain ⟨F₂, hF₂c, hF₂el, hF₂card, hxF₂⟩ := D.exists_E6 IU hc₂ hV2
  have hcomm : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := fun a ha b hb =>
    comm_of_ne hc₁ hc₂ hne (hF₁c ha) (hF₂c hb)
  obtain ⟨h1, -, -, -⟩ := IU Y c₁ hc₁.2.2 (D.hK.subgroup c₁) ⟨V, D.le_centerOf hc₁ hV1, D.hVel, D.hV9⟩
  have hinf : Nat.card (F₁ ⊓ F₂ : Subgroup Y) ≤ 9 := by
    refine h1 _ ?_ (isElemAbelian_mono hF₁el inf_le_left)
    intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
    exact mem_centerOf_iff.2 ⟨hF₁c hu1, fun k hk => (comm_of_ne hc₁ hc₂ hne hk (hF₂c hu2)).symm⟩
  have hsup := card_mul_le_card_sup_mul_inf hcomm
  rw [hF₁card, hF₂card] at hsup
  have hE : 3 ^ 10 ≤ Nat.card (F₁ ⊔ F₂ : Subgroup Y) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (F₁ ⊔ F₂ : Subgroup Y) * Nat.card (F₁ ⊓ F₂ : Subgroup Y) < 3 ^ 10 * 9 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hinf (by norm_num)
    norm_num at hsup this
    omega
  have hF₁F₂ : F₁ ≤ Subgroup.centralizer (F₂ : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
  have hEel : IsElemAbelian 3 (F₁ ⊔ F₂) := isElemAbelian_sup_of_commute hF₁el hF₂el hF₁F₂
  have hxE : x ∈ Subgroup.normalizer ((F₁ ⊔ F₂ : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have e1 := mem_normalizer_iff_gLBConj_eq.1 hxF₁
    have e2 := mem_normalizer_iff_gLBConj_eq.1 hxF₂
    unfold GLBConj at e1 e2 ⊢
    rw [Subgroup.map_sup, e1, e2]
  have hfix := card_le_cube_fixed hEel hxE D.hx3
  have hCel : IsElemAbelian 3 ((F₁ ⊔ F₂) ⊓ Subgroup.centralizer ({x} : Set Y)) :=
    isElemAbelian_mono hEel inf_le_left
  have hlt := D.hrk _ inf_le_right hCel
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (Lemma118T.isPGroup_of_isElemAbelian hCel)
  rw [hk] at hfix hlt
  have hk4 : 4 ≤ k := by
    by_contra h
    push Not at h
    have : (3 ^ k) ^ 3 ≤ (3 ^ 3) ^ 3 :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 3
    norm_num at this
    omega
  have : 81 ≤ 3 ^ k := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
  omega

theorem false_of_one (IU : InputU43) (D : CentralData Y V x) {c : Subgroup Y}
    (hc : IsComponentOf c (⊤ : Subgroup Y))
    (hall : ∀ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) → c' = c) : False := by
  have heq : GLAPLayer 3 (⊤ : Subgroup Y) = c :=
    le_antisymm (layer_le_of D.hO fun c' hc' => (hall c' hc').le) (comp_le_layer D.hO hc)
  have hVc : V ≤ c := heq ▸ D.hVL
  obtain ⟨-, -, h3, -⟩ := IU Y c hc.2.2 (D.hK.subgroup c) ⟨V, D.le_centerOf hc hVc, D.hVel, D.hV9⟩
  refine h3 V (D.le_centerOf hc hVc) D.hVel D.hV9 fun z hz hz1 w hw hw1 => ?_
  obtain ⟨n, hn⟩ := D.htr z hz hz1 w hw hw1
  haveI : (GLAPLayer 3 (⊤ : Subgroup Y)).Normal := Lemma1113b.layer_top_normal D.hO
  have hnN : n ∈ Subgroup.normalizer (c : Set Y) := by
    rw [← heq, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top n
  exact ⟨n, hnN, hn⟩

end CentralData

end CentralCases

section Simple

variable {Y : Type} [Group Y] [Finite Y]

theorem simple_core (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥)
    (hL : GLAPLayer 3 (⊤ : Subgroup Y) ≠ ⊥) {V : Subgroup Y}
    (hVL : V ≤ GLAPLayer 3 (⊤ : Subgroup Y)) (hVel : IsElemAbelian 3 V) (hV9 : Nat.card V = 9)
    {x : Y} (hx3 : x ^ 3 = 1) (hxV : ∀ v ∈ V, x * v = v * x)
    (hsolv : IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set Y)))
    (hrk : ∀ F : Subgroup Y, F ≤ Subgroup.centralizer ({x} : Set Y) → IsElemAbelian 3 F →
      Nat.card F < 81)
    (htr : ∀ z ∈ V, z ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ n : Y, n⁻¹ * z * n = w)
    {R : Subgroup Y} (hR : IsSylowIn 3 (⊤ : Subgroup Y) R)
    (hZ : ∀ z ∈ R, (∀ r ∈ R, r * z = z * r) → z ^ 3 = 1 → z ∈ V) :
    CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (⊤ : Subgroup Y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have lemZ : ∀ c₀ : Subgroup Y, IsComponentOf c₀ (⊤ : Subgroup Y) →
      (∀ z ∈ V, ∀ u ∈ c₀, z * u = u * z) → False := by
    intro c₀ hc₀ hV
    obtain ⟨z, hzN, hzR, hzc, hz1, hz3⟩ := exists_central_mem_orbit hO hR hc₀
    exact hz1 (eq_one_of_mem_orbit hO hO3 hc₀ hzN
      (centralizes_orbit (hV z (hZ z hzR hzc hz3)) hzc))
  have hex : ∃ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) := by
    by_contra hne
    push Not at hne
    exact hL (le_bot_iff.1 (layer_le_of hO fun c hc => (hne c hc).elim))
  by_cases hsingle : ∃ c₁ : Subgroup Y, IsComponentOf c₁ (⊤ : Subgroup Y) ∧
      ∀ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) → c = c₁
  · obtain ⟨c₁, hc₁, hall⟩ := hsingle
    have heq : GLAPLayer 3 (⊤ : Subgroup Y) = c₁ :=
      le_antisymm (layer_le_of hO fun c hc => (hall c hc).le) (comp_le_layer hO hc₁)
    rw [heq]
    exact hc₁.2.2
  exfalso
  push Not at hsingle
  by_cases hcase1 : ∃ z ∈ V, z ≠ 1 ∧ ∃ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) ∧ z ∈ c
  · obtain ⟨z, hzV, hz1, c, hc, hzc⟩ := hcase1
    have hall : ∀ w ∈ V, w ≠ 1 → ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧ w ∈ c' := by
      intro w hwV hw1
      obtain ⟨n, hn⟩ := htr z hzV hz1 w hwV hw1
      refine ⟨GLBConj n c, isComp_conj hc n, mem_gLBConj.2 ?_⟩
      rw [← hn]
      convert hzc using 1
      group
    have hVc : ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧ V ≤ c' := by
      by_contra hno
      push Not at hno
      obtain ⟨w, hwV, hwc⟩ := Set.not_subset.1 (hno c hc)
      have hw1 : w ≠ 1 := fun h => hwc (h ▸ c.one_mem)
      obtain ⟨c', hc', hwc'⟩ := hall w hwV hw1
      have hcc' : c ≠ c' := fun h => hwc (h ▸ hwc')
      have hzw1 : z * w ≠ 1 := fun h => hwc (by
        rw [eq_inv_of_mul_eq_one_right h]
        exact c.inv_mem hzc)
      obtain ⟨c'', hc'', hzwc''⟩ := hall (z * w) (V.mul_mem hzV hwV) hzw1
      by_cases h1 : c'' = c
      · apply hwc
        have e : w = z⁻¹ * (z * w) := by group
        rw [e]
        exact c.mul_mem (c.inv_mem hzc) (h1 ▸ hzwc'')
      by_cases h2 : c'' = c'
      · have hzc' : z ∈ c' := by
          have e : z = (z * w) * w⁻¹ := by group
          rw [e]
          exact c'.mul_mem (h2 ▸ hzwc'') (c'.inv_mem hwc')
        exact hz1 (eq_one_of_central hO hO3 hc hzc fun v hv =>
          comm_of_ne hc' hc (Ne.symm hcc') hzc' hv)
      · apply hzw1
        refine eq_one_of_central hO hO3 hc'' hzwc'' fun v hv => ?_
        have h1' := comm_of_ne hc hc'' (fun e => h1 e.symm) hzc hv
        have h2' := comm_of_ne hc' hc'' (fun e => h2 e.symm) hwc' hv
        calc z * w * v = z * (w * v) := mul_assoc _ _ _
          _ = z * (v * w) := by rw [h2']
          _ = (z * v) * w := (mul_assoc _ _ _).symm
          _ = (v * z) * w := by rw [h1']
          _ = v * (z * w) := mul_assoc _ _ _
    obtain ⟨c', hc', hVc'⟩ := hVc
    obtain ⟨cs, hcs, hne⟩ := hsingle c' hc'
    exact lemZ cs hcs fun z hz u hu => comm_of_ne hc' hcs (Ne.symm hne) (hVc' hz) hu
  by_cases hcase2 : ∃ z ∈ V, z ≠ 1 ∧ ∃ c : Subgroup Y, IsComponentOf c (⊤ : Subgroup Y) ∧
      ∀ u ∈ c, z * u = u * z
  · obtain ⟨z, hzV, hz1, c, hc, hzc⟩ := hcase2
    have hall : ∀ w ∈ V, w ≠ 1 → ∃ c' : Subgroup Y, IsComponentOf c' (⊤ : Subgroup Y) ∧
        ∀ u ∈ c', w * u = u * w := by
      intro w hwV hw1
      obtain ⟨n, hn⟩ := htr z hzV hz1 w hwV hw1
      refine ⟨GLBConj n c, isComp_conj hc n, fun u hu => ?_⟩
      have h1 := hzc _ (mem_gLBConj.1 hu)
      rw [← hn]
      calc n⁻¹ * z * n * u = n⁻¹ * (z * (n * u * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * u * n⁻¹) * z) * n := by rw [h1]
        _ = u * (n⁻¹ * z * n) := by group
    obtain ⟨c₁, hc₁⟩ := hex
    obtain ⟨z₀, -, hz₀R, hz₀c, hz₀1, hz₀3⟩ := exists_central_mem_orbit hO hR hc₁
    have hz₀V := hZ z₀ hz₀R hz₀c hz₀3
    obtain ⟨c₀, hc₀, hz₀c₀⟩ := hall z₀ hz₀V hz₀1
    obtain ⟨z', hz'N, hz'R, hz'c, hz'1, hz'3⟩ := exists_central_mem_orbit hO hR hc₀
    have hz'V := hZ z' hz'R hz'c hz'3
    have hz₀N := centralizes_orbit hz₀c₀ hz₀c
    have hz'nz : z' ∉ Subgroup.zpowers z₀ := by
      intro hmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
      apply hz'1
      refine eq_one_of_mem_orbit hO hO3 hc₀ hz'N fun y hy => ?_
      exact ((show Commute z₀ y from hz₀N y hy).zpow_left k).eq
    have hzz1 : z₀ * z' ≠ 1 := fun h => hz'nz (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z₀))
    obtain ⟨cs, hcs, hzzcs⟩ := hall (z₀ * z') (V.mul_mem hz₀V hz'V) hzz1
    have hboth : (∀ u ∈ cs, z₀ * u = u * z₀) ∧ ∀ u ∈ cs, z' * u = u * z' := by
      rcases comp_le_or_centralizes (R := R) hc₀ hcs with hle | hcen
      · have h0 : ∀ u ∈ cs, z₀ * u = u * z₀ := fun u hu => hz₀N u (hle hu)
        refine ⟨h0, fun u hu => ?_⟩
        have h1 := hzzcs u hu
        have h2 := h0 u hu
        calc z' * u = z₀⁻¹ * ((z₀ * z') * u) := by group
          _ = z₀⁻¹ * (u * (z₀ * z')) := by rw [h1]
          _ = z₀⁻¹ * (u * z₀) * z' := by group
          _ = z₀⁻¹ * (z₀ * u) * z' := by rw [h2]
          _ = u * z' := by group
      · have h1 : ∀ u ∈ cs, z' * u = u * z' := fun u hu => hcen z' hz'N u hu
        refine ⟨fun u hu => ?_, h1⟩
        have h2 := hzzcs u hu
        have h3 := h1 u hu
        calc z₀ * u = ((z₀ * z') * (z'⁻¹ * u * z')) * z'⁻¹ := by group
          _ = ((z₀ * z') * u) * z'⁻¹ := by
              rw [show z'⁻¹ * u * z' = u by rw [mul_assoc, ← h3]; group]
          _ = (u * (z₀ * z')) * z'⁻¹ := by rw [h2]
          _ = u * z₀ := by group
    have hcomm : z' * z₀ = z₀ * z' := hVel.comm hz'V hz₀V
    obtain ⟨-, hcard⟩ := Claims11x.plane_of_commute hz'3 hz₀3 hz₀1 hcomm hz'nz
    have hVeq : Subgroup.zpowers z' ⊔ Subgroup.zpowers z₀ = V :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.2 hz'V)
        (Subgroup.zpowers_le.2 hz₀V)) (by rw [hV9, hcard])
    refine lemZ cs hcs fun v hv u hu => ?_
    rw [← hVeq] at hv
    have hle : Subgroup.zpowers z' ⊔ Subgroup.zpowers z₀ ≤ Subgroup.centralizer ({u} : Set Y) :=
      sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hboth.2 u hu)))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hboth.1 u hu)))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv)
  push Not at hcase1 hcase2
  obtain ⟨c₁, hc₁⟩ := hex
  set C₁ : Subgroup Y := Subgroup.centralizer (c₁ : Set Y) with hC₁
  have hxN : x ∈ Subgroup.normalizer (c₁ : Set Y) := mem_normalizer_comp hO hO3 hx3 hsolv hc₁
  have hxC : x ∈ Subgroup.normalizer (C₁ : Set Y) := mem_normalizer_centralizer hxN
  have hVN : V ≤ Subgroup.normalizer (C₁ : Set Y) := fun v hv =>
    mem_normalizer_centralizer (layer_le_normalizer hO hc₁ (hVL hv))
  have hVC : ∀ z ∈ V, z ∈ C₁ → z = 1 := by
    intro z hzV hzC
    by_contra hz1
    obtain ⟨u, hu, hne⟩ := hcase2 z hzV hz1 c₁ hc₁
    exact hne (Subgroup.mem_centralizer_iff.1 hzC u hu).symm
  have hdec : ∀ z ∈ V, ∃ u ∈ c₁, ∃ n ∈ C₁, u * n = z := fun z hz => exists_decomp hO hc₁ (hVL hz)
  set P : Subgroup Y := (V ⊔ C₁) ⊓ c₁ with hP
  have hPmem : ∀ u ∈ P, u ∈ c₁ ∧ ∃ z ∈ V, ∃ n ∈ C₁, z * n = u := fun u hu =>
    ⟨(Subgroup.mem_inf.1 hu).2, Inputs1114.exists_mul_of_mem_sup hVN (Subgroup.mem_inf.1 hu).1⟩
  have hcn : ∀ u ∈ c₁, ∀ n ∈ C₁, u * n = n * u := fun u hu n hn =>
    Subgroup.mem_centralizer_iff.1 hn u hu
  have hcomm : ∀ u ∈ P, ∀ w ∈ V, u * w = w * u := by
    intro u hu w hw
    obtain ⟨huc, z, hzV, n, hn, hzn⟩ := hPmem u hu
    obtain ⟨uw, huw, nw, hnw, hw'⟩ := hdec w hw
    have hzw : z * w = w * z := hVel.comm hzV hw
    have hz : z = u * n⁻¹ := by rw [← hzn]; group
    have h1 : u * uw = uw * u := by
      refine decomp_unique hO hO3 hc₁ (c₁.mul_mem huc huw) (c₁.mul_mem huw huc)
        (C₁.mul_mem (C₁.inv_mem hn) hnw) (C₁.mul_mem hnw (C₁.inv_mem hn)) ?_
      have e1 : u * uw * (n⁻¹ * nw) = z * w := by
        rw [hz, ← hw']
        calc u * uw * (n⁻¹ * nw) = u * (uw * n⁻¹) * nw := by group
          _ = u * (n⁻¹ * uw) * nw := by rw [hcn uw huw n⁻¹ (C₁.inv_mem hn)]
          _ = u * n⁻¹ * (uw * nw) := by group
      have e2 : uw * u * (nw * n⁻¹) = w * z := by
        rw [hz, ← hw']
        calc uw * u * (nw * n⁻¹) = uw * (u * nw) * n⁻¹ := by group
          _ = uw * (nw * u) * n⁻¹ := by rw [hcn u huc nw hnw]
          _ = uw * nw * (u * n⁻¹) := by group
      rw [e1, e2, hzw]
    rw [← hw']
    calc u * (uw * nw) = (u * uw) * nw := (mul_assoc _ _ _).symm
      _ = (uw * u) * nw := by rw [h1]
      _ = uw * (u * nw) := mul_assoc _ _ _
      _ = uw * (nw * u) := by rw [hcn u huc nw hnw]
      _ = uw * nw * u := (mul_assoc _ _ _).symm
  have hPel : IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
    · obtain ⟨hbc, z', hz'V, n', hn', hzn'⟩ := hPmem b b.2
      change (a : Y) * b = b * a
      rw [← hzn']
      have hac : (a : Y) ∈ c₁ := (hPmem a a.2).1
      calc (a : Y) * (z' * n') = (a * z') * n' := (mul_assoc _ _ _).symm
        _ = (z' * a) * n' := by rw [hcomm a a.2 z' hz'V]
        _ = z' * (a * n') := mul_assoc _ _ _
        _ = z' * (n' * a) := by rw [hcn a hac n' hn']
        _ = z' * n' * a := (mul_assoc _ _ _).symm
    · obtain ⟨huc, z, hzV, n, hn, hzn⟩ := hPmem u hu
      have hz : z = u * n⁻¹ := by rw [← hzn]; group
      have hcom : Commute u n⁻¹ := hcn u huc n⁻¹ (C₁.inv_mem hn)
      have h3 : u ^ 3 * (n⁻¹) ^ 3 = 1 := by
        rw [← hcom.mul_pow, ← hz]
        exact hVel.2 z hzV
      have h4 := decomp_unique hO hO3 hc₁ (c₁.pow_mem huc 3) c₁.one_mem
        (C₁.pow_mem (C₁.inv_mem hn) 3) C₁.one_mem (h3.trans (mul_one 1).symm)
      exact h4
  have hPx : P ≤ Subgroup.centralizer ({x} : Set Y) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨huc, z, hzV, n, hn, hzn⟩ := hPmem u hu
    have hz : z = u * n⁻¹ := by rw [← hzn]; group
    have hxu : x * u * x⁻¹ ∈ c₁ := (Subgroup.mem_normalizer_iff.1 hxN u).1 huc
    have hxn : x * n⁻¹ * x⁻¹ ∈ C₁ := (Subgroup.mem_normalizer_iff.1 hxC n⁻¹).1 (C₁.inv_mem hn)
    have hxz : x * z * x⁻¹ = z := by rw [hxV z hzV]; group
    have h1 : x * u * x⁻¹ = u := by
      refine decomp_unique hO hO3 hc₁ hxu huc hxn (C₁.inv_mem hn) ?_
      rw [← hz, ← hxz, hz]
      group
    calc u * x = (x * u * x⁻¹) * x := by rw [h1]
      _ = x * u := by group
  have hdec' : ∀ z : ↥V, ∃ u : ↥P, ∃ n ∈ C₁, (u : Y) * n = z := by
    intro z
    obtain ⟨u, hu, n, hn, hun⟩ := hdec z z.2
    have hu' : u = (z : Y) * n⁻¹ := by rw [← hun]; group
    refine ⟨⟨u, Subgroup.mem_inf.2 ⟨?_, hu⟩⟩, n, hn, hun⟩
    rw [hu']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left z.2) (Subgroup.mem_sup_right (C₁.inv_mem hn))
  choose f hf using hdec'
  have hfinj : Function.Injective f := by
    intro z w hzw
    obtain ⟨n, hn, hzn⟩ := hf z
    obtain ⟨n', hn', hwn⟩ := hf w
    rw [hzw] at hzn
    have hmem : (z : Y)⁻¹ * w ∈ C₁ := by
      rw [← hzn, ← hwn]
      have e : ((f w : Y) * n)⁻¹ * ((f w : Y) * n') = n⁻¹ * n' := by group
      rw [e]
      exact C₁.mul_mem (C₁.inv_mem hn) hn'
    have h1 := hVC _ (V.mul_mem (V.inv_mem z.2) w.2) hmem
    apply Subtype.ext
    calc (z : Y) = z * ((z : Y)⁻¹ * w) := by rw [h1, mul_one]
      _ = w := by group
  have hPcard : 9 ≤ Nat.card P := hV9 ▸ Nat.card_le_card_of_injective f hfinj
  have hdisj : V ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzV, hzP⟩ := Subgroup.mem_inf.1 hz
    by_contra hz1
    exact hcase1 z hzV hz1 c₁ hc₁ (Subgroup.mem_inf.1 hzP).2
  have hVP : V ≤ Subgroup.centralizer (P : Set Y) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun u hu => hcomm u hu v hv
  have hEel := isElemAbelian_sup_of_commute hVel hPel hVP
  have hEcard := CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute
    (fun v hv u hu => (hcomm u hu v hv).symm) hdisj
  have hEle : V ⊔ P ≤ Subgroup.centralizer ({x} : Set Y) :=
    sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (hxV v hv).symm) hPx
  have h81 := hrk _ hEle hEel
  rw [hEcard, hV9] at h81
  omega

end Simple

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_subgroupOf {p : ℕ} {H S : Subgroup G} (hS : IsElemAbelian p S) :
    IsElemAbelian p (S.subgroupOf H) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · have ha : ((a : ↥H) : G) ∈ S := Subgroup.mem_subgroupOf.1 a.2
    have hb : ((b : ↥H) : G) ∈ S := Subgroup.mem_subgroupOf.1 b.2
    exact hS.comm ha hb
  · have hx' : ((x : ↥H) : G) ∈ S := Subgroup.mem_subgroupOf.1 hx
    simpa using hS.2 _ hx'

theorem exists_tilde_data (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (hSolv : Claims11x.Lemma1113SolvClaim) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K)
    (hL : GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥) :
    ∃ (V : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) (x : ↥M ⧸ GLAPPrimeCore 3 ↥M)
      (R : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)),
      CFSG.Open.IsKGroup (↥M ⧸ GLAPPrimeCore 3 ↥M) ∧
      V ≤ GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ∧ IsElemAbelian 3 V ∧
      Nat.card V = 9 ∧ x ^ 3 = 1 ∧ (∀ v ∈ V, x * v = v * x) ∧ x ∉ V ∧
      IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) ∧
      (∀ F : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
        F ≤ Subgroup.centralizer ({x} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) → IsElemAbelian 3 F →
          Nat.card F < 81) ∧
      (∀ z ∈ V, z ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ n : ↥M ⧸ GLAPPrimeCore 3 ↥M, n⁻¹ * z * n = w) ∧
      IsSylowIn 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) R ∧
      (∀ z ∈ R, (∀ r ∈ R, r * z = z * r) → z ^ 3 = 1 → z ∈ V) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  have hN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have ha : a ∈ A := h.ha.1
  have haM : a ∈ M := hAM ha
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  set a' : ↥M := ⟨a, haM⟩ with ha'
  have ha3' : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hinj3 : ∀ {T : Subgroup ↥M}, IsPGroup 3 ↥T → ∀ x ∈ T, ∀ y ∈ T, π x = π y → x = y := by
    intro T hT x hx y hy hxy
    have hmem : x⁻¹ * y ∈ GLAPPrimeCore 3 ↥M := (QuotientGroup.eq).1 hxy
    have h1 := Claims11x.eq_one_of_mem_coprime hN hT hmem (T.mul_mem (T.inv_mem hx) hy)
    rw [inv_mul_eq_one] at h1
    exact h1
  have hMne : M ≠ ⊤ := isTwoLocal_ne_top h.standing h.pre.1.1
  have hKM : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper h.standing.kProper hMne
  have hKY : CFSG.Open.IsKGroup (↥M ⧸ GLAPPrimeCore 3 ↥M) := hKM.quotient (GLAPPrimeCore 3 ↥M)
  have hA0el : IsElemAbelian 3 (E ⊓ A) := isElemAbelian_mono hAel inf_le_right
  set A0 : Subgroup ↥M := (E ⊓ A).subgroupOf M with hA0
  have hA0el' : IsElemAbelian 3 A0 := isElemAbelian_subgroupOf hA0el
  have hA0p : IsPGroup 3 ↥A0 := Lemma118T.isPGroup_of_isElemAbelian hA0el'
  set V : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) := A0.map π with hV
  have hVel : IsElemAbelian 3 V := CFSG.SectionRank.isElemAbelian_map hA0el' π
  have hV9 : Nat.card V = 9 := by
    have h1 := (Claims11x.isElemAbelian_of_injOn π (hinj3 hA0p) hVel).2
    have h2 : Nat.card A0 = Nat.card (E ⊓ A : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hAM)).toEquiv
    have h3 : Nat.card (E ⊓ A : Subgroup G) = 9 := by
      rw [Lemma1114.card_eq_pow_of_pRank hA0el, (h119 h).1]
      norm_num
    rw [← h1, h2, h3]
  have hVL : V ≤ GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rintro _ ⟨e, he, rfl⟩
    have he' : (e : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 he
    by_cases he1 : (e : G) = 1
    · have : e = 1 := Subtype.ext he1
      rw [this, map_one]
      exact Subgroup.one_mem _
    · exact Claims11x.tilde_mem_layer h1111 h1112 h119 h104ii h rfl (e : G) e.2 he' he1 hL
  have hx3 : π a' ^ 3 = 1 := by rw [← map_pow, ha3', map_one]
  have hxV : ∀ v ∈ V, π a' * v = v * π a' := by
    rintro _ ⟨e, he, rfl⟩
    have he' : (e : G) ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 he)).2
    have hc : a' * e = e * a' := Subtype.ext (hAel.comm ha he')
    rw [← map_mul, ← map_mul, hc]
  have hxnV : π a' ∉ V := by
    rintro ⟨e, he, hea⟩
    have hAp : IsPGroup 3 ↥(A.subgroupOf M) :=
      Lemma118T.isPGroup_of_isElemAbelian (isElemAbelian_subgroupOf hAel)
    have he' : (e : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 he
    have heq := hinj3 hAp e (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 he').2) a'
      (Subgroup.mem_subgroupOf.2 ha) hea
    apply h.notD
    refine ⟨E, h.pair.1.1, ?_⟩
    have : (e : G) = a := congrArg Subtype.val heq
    rw [← this]
    exact (Subgroup.mem_inf.1 he').1
  have hord : ∃ k : ℕ, orderOf a' = 3 ^ k := by
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha3')
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hcent : Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) =
      (Subgroup.centralizer ({a'} : Set ↥M)).map π :=
    CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map 3 hord
  have hsolv : IsPSolvable 3 ↥(Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
    have hS := hSolv G m 3 B M E A a K h rfl
    have heq : (M ⊓ Cg a).subgroupOf M = Subgroup.centralizer ({a'} : Set ↥M) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2)
      · intro hx
        exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val hx)⟩
    have hS' : IsPSolvable 3 ↥(Subgroup.centralizer ({a'} : Set ↥M)) := by
      rw [← heq]
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left).symm hS
    rw [hcent]
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map π hS'
  have hCa : CFSG.Open.pRank 3 (Cg a) = 3 := ((h1112 h).1).2
  have hrk : ∀ F : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
      F ≤ Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) → IsElemAbelian 3 F →
        Nat.card F < 81 := by
    intro F hFC hFel
    obtain ⟨T, hTC, -, hTm, hinj⟩ := Claims11x.exists_lift_centralizer haM ha3 hFC
      (Lemma118T.isPGroup_of_isElemAbelian hFel)
    rw [← hTm] at hFel
    obtain ⟨hTel, hTcard⟩ := Claims11x.isElemAbelian_of_injOn π hinj hFel
    have hTG : T.map M.subtype ≤ Cg a := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : y * a' = a' * y := Subgroup.mem_centralizer_singleton_iff.1 (hTC hy)
      exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
    have hTGel : IsElemAbelian 3 (T.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hTel _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (Lemma118T.isPGroup_of_isElemAbelian hTGel)
    have hk3 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hTG hTGel hk
    rw [hCa] at hk3
    have hcardF : Nat.card F = 3 ^ k := by
      rw [← hTm, ← hTcard, ← hk, Subgroup.card_map_of_injective M.subtype_injective]
    rw [hcardF]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ < 81 := by norm_num
  have hIL : IsLThreeFour (barOf 3 K) := (h1111 h).2.2
  have htr : ∀ z ∈ V, z ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ n : ↥M ⧸ GLAPPrimeCore 3 ↥M, n⁻¹ * z * n = w := by
    rintro _ ⟨e, he, rfl⟩ hz1 _ ⟨f, hf, rfl⟩ hw1
    have he' : (e : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 he
    have hf' : (f : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hf
    have he1 : (e : G) ≠ 1 := fun h1 => hz1 (by rw [show e = 1 from Subtype.ext h1, map_one])
    have hf1 : (f : G) ≠ 1 := fun h1 => hw1 (by rw [show f = 1 from Subtype.ext h1, map_one])
    obtain ⟨n, -, hnN, hne⟩ := Inputs1114.lemma1114FusionInput_of_inputs h119 h1112 h rfl hIL
      (e : G) he' he1 (f : G) hf' hf1
    have hnM : n ∈ M := l1110_normalizer_A0_le h.pair.1.1 (h119 h).1 hnN
    refine ⟨π ⟨n, hnM⟩, ?_⟩
    have heq : (⟨n, hnM⟩ : ↥M)⁻¹ * e * ⟨n, hnM⟩ = f := Subtype.ext (by simpa using hne)
    rw [← map_inv, ← map_mul, ← map_mul, heq]
  obtain ⟨R, hR, hAR⟩ := Lemma1112b.exists_isSylowIn_ge hAM (Lemma118T.isPGroup_of_isElemAbelian hAel)
  have hR' := Claims11x.isSylowIn_top_subgroupOf hR
  set R' : Subgroup ↥M := R.subgroupOf M with hR'def
  have hR'3 : IsPGroup 3 ↥R' := hR'.2.1
  have hRt : IsSylowIn 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) (R'.map π) := by
    refine ⟨le_top, hR'3.map π, fun S _ hS3 hRS => ?_⟩
    have hSH : S ≤ (⊤ : Subgroup ↥M).map π := by
      rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      exact le_top
    obtain ⟨T, hRT, -, hT3, hTm, -⟩ :=
      Claims11x.exists_lift_of_coprime (GLAPPrimeCore 3 ↥M) hN hSH hS3 le_top hR'3 hRS
    have hTR : T = R' := hR'.2.2 T le_top hT3 hRT
    rw [← hTm, hTR]
  have hZ : ∀ z ∈ R'.map π, (∀ r ∈ R'.map π, r * z = z * r) → z ^ 3 = 1 → z ∈ V := by
    rintro _ ⟨y, hy, rfl⟩ hzc hz3
    have hyc : ∀ r ∈ R', r * y = y * r := fun r hr =>
      hinj3 hR'3 _ (R'.mul_mem hr hy) _ (R'.mul_mem hy hr) (by
        rw [map_mul, map_mul]
        exact hzc _ ⟨r, hr, rfl⟩)
    have hy3 : y ^ 3 = 1 := hinj3 hR'3 _ (R'.pow_mem hy 3) _ R'.one_mem (by rw [map_pow, hz3, map_one])
    have hyc' : ∀ g ∈ R, g * (y : G) = y * g := fun g hg =>
      congrArg Subtype.val (hyc ⟨g, hR.1 hg⟩ (Subgroup.mem_subgroupOf.2 hg))
    have hy3' : (y : G) ^ 3 = 1 := by
      have := congrArg Subtype.val hy3
      simpa using this
    have hyA0 := Claims11x.mem_A0_of_central h1112 h104ii h hR hAR hyc' hy3'
    exact ⟨y, Subgroup.mem_subgroupOf.2 hyA0, rfl⟩
  exact ⟨V, π a', R'.map π, hKY, hVL, hVel, hV9, hx3, hxV, hxnV, hsolv, hrk, htr, hRt, hZ⟩

theorem lemma1113SimpleClaim_of_inputs (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    (hSolv : Claims11x.Lemma1113SolvClaim) : Claims11x.Lemma1113SimpleClaim := by
  intro G _ _ m p B M E A a K h hp hL hO3
  subst hp
  obtain ⟨V, x, R, -, hVL, hVel, hV9, hx3, hxV, -, hsolv, hrk, htr, hRt, hZ⟩ :=
    exists_tilde_data h1111 h1112 h119 h104ii hSolv h hL
  exact simple_core (CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3) hO3 hL hVL hVel hV9 hx3 hxV
    hsolv hrk htr hRt hZ

theorem le_of_normal_three {Y : Type} [Group Y] [Finite Y] {V R N : Subgroup Y}
    (hR : IsSylowIn 3 (⊤ : Subgroup Y) R)
    (hZ : ∀ z ∈ R, (∀ r ∈ R, r * z = z * r) → z ^ 3 = 1 → z ∈ V)
    (htr : ∀ z ∈ V, z ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ n : Y, n⁻¹ * z * n = w)
    (hN : N.Normal) (h3 : 3 ∣ Nat.card N) : V ≤ N := by
  haveI := hN
  obtain ⟨z, hzN, hzR, hzc, hz1, hz3⟩ :=
    exists_central_mem hR le_top (le_of_eq (Subgroup.normalizer_eq_top (H := N)).symm) h3
  have hzV := hZ z hzR hzc hz3
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact N.one_mem
  obtain ⟨n, hn⟩ := htr z hzV hz1 w hw hw1
  rw [← hn]
  have := hN.conj_mem z hzN n⁻¹
  simpa using this

theorem lemma1113SimpleClaim_of_inputs' (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement) (h111 : Prop111Statement)
    (hNorm : Claims11x.InputL34SylowNormalizer) : Claims11x.Lemma1113SimpleClaim :=
  lemma1113SimpleClaim_of_inputs h1111 h1112 h119 h104ii
    (Claims11x.lemma1113SolvClaim_of_inputs h1111 h1112 h119 h111 hNorm)

end Bridge

section Input295

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)

@[expose] def Input29_5' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) →
      x ∉ L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 4 ∧
      (∀ Q : Subgroup X, IsSylowIn 3 (L ⊓ Subgroup.centralizer ({x} : Set X)) Q →
        (∀ q ∈ Q, q ^ 3 = 1) ∧ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁) ∧
      (∀ D : Subgroup X, D ≤ L → IsElemAbelian 3 D → Nat.card D = 9 →
        ∃ E₀ : Subgroup X, D ≤ E₀ ∧ E₀ ≤ L ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 81)

theorem input29_5_of' (h : Input29_5') : Claims11x.Input29_5 := by
  intro X _ _ L hLn hq hK hC hchev hrk x hx hC4 hrk3 hsolv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h1, h2, h3, h4⟩ := h X L hLn hq hK hC hchev hrk x hx hC4 hrk3 hsolv
  refine ⟨h1, h2, h3, fun D hD hDel hD9 => ?_⟩
  obtain ⟨E₀, hDE₀, hE₀L, hE₀el, hE₀81⟩ := h4 D (hD.trans inf_le_left) hDel hD9
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  set C : Subgroup X := L ⊓ Subgroup.centralizer (D : Set X) with hCdef
  have hE₀C : E₀ ≤ C := by
    refine le_inf hE₀L fun e he => Subgroup.mem_centralizer_iff.2 fun d hd => ?_
    exact hE₀el.comm (hDE₀ hd) he
  have hxD : ∀ d ∈ D, x * d = d * x := fun d hd =>
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hD hd)).2).symm
  haveI := hLn
  have hxL : x ∈ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  have hxDn : x ∈ Subgroup.normalizer (D : Set X) :=
    Subgroup.centralizer_le_normalizer (D : Set X)
      (Subgroup.mem_centralizer_iff.2 fun d hd => (hxD d hd).symm)
  have hxCD := mem_normalizer_centralizer hxDn
  have hxC : x ∈ Subgroup.normalizer (C : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := Subgroup.mem_normalizer_iff.1 hxL w
    have h2 := Subgroup.mem_normalizer_iff.1 hxCD w
    exact and_congr h1 h2
  obtain ⟨R, hR, hxR, hS, -⟩ := exists_sylow_normalized hxC hx3
  obtain ⟨c, hcC, hc⟩ := Claims11x.exists_conj_le_of_isSylowIn hS hE₀C
    (Lemma118T.isPGroup_of_isElemAbelian hE₀el)
  have hcD : ∀ d ∈ D, c * d = d * c := fun d hd =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcC).2 d hd).symm
  have hER : GLBConj c E₀ ≤ R := by
    intro w hw
    have hw' : c * w * c⁻¹ ∈ E₀ := mem_gLBConj.1 hw
    have e : w = c⁻¹ * (c * w * c⁻¹) * c := by group
    rw [e]
    exact (Subgroup.mem_inf.1 (hc _ hw')).1
  refine ⟨GLBConj c E₀, fun d hd => mem_gLBConj.2 ?_, fun w hw => ?_,
    Lemma118T.isElemAbelian_gLBConj' hE₀el c, by rw [Lemma1112b.card_glbConj, hE₀81], ?_⟩
  · rw [hcD d hd, mul_assoc, mul_inv_cancel, mul_one]
    exact hDE₀ hd
  · have hw' : c * w * c⁻¹ ∈ E₀ := mem_gLBConj.1 hw
    have e : w = c⁻¹ * (c * w * c⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact hLn.conj_mem _ (hE₀L hw') c⁻¹
  · exact hR.2.1.to_le (sup_le hER (Subgroup.zpowers_le.2 hxR))

end Input295

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1113
