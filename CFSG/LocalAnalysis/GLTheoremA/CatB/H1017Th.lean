module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Ly
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

@[expose] def TwoLocalBound27 (G : Type) [Group G] : Prop :=
  ∀ R E : Subgroup G, R ≠ ⊥ → IsPGroup 2 R → E ≤ Subgroup.normalizer (R : Set G) →
    IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3

theorem comm_of_elemAbelian' {X : Type} [Group X] {p : ℕ} {E : Subgroup X} (hE : IsElemAbelian p E)
    {x y : X} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI := hE.1
  have := congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  simpa using this

theorem twoLocalBound27_of_mulEquiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (h : TwoLocalBound27 H) : TwoLocalBound27 G := by
  intro R E hR hR2 hEN hE
  have hR' : R.map φ.toMonoidHom ≠ ⊥ := fun h0 =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R φ.injective).1 h0)
  have hR2' : IsPGroup 2 (R.map φ.toMonoidHom) := hR2.map _
  have hEN' : E.map φ.toMonoidHom ≤
      Subgroup.normalizer ((R.map φ.toMonoidHom : Subgroup H) : Set H) :=
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map _)
  have hE' : IsElemAbelian 3 (E.map φ.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      show φ x * φ y = φ y * φ x
      rw [← map_mul, ← map_mul, comm_of_elemAbelian' hE hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      show φ x ^ 3 = 1
      rw [← map_pow, hE.2 x hx, map_one]
  have := h _ _ hR' hR2' hEN' hE'
  rwa [Subgroup.card_map_of_injective φ.injective] at this

theorem involution_data_of_conj {X : Type} [Group X] [Finite X] {a : X}
    (ha : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({a} : Set X) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ 3)
    (hb : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({a} : Set X) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ 3 → ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) →
        u * a = a * u → u = a)
    {t : X} (ht : IsConj a t) :
    (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ 3) ∧
    (∀ F : Subgroup X, F ≤ Subgroup.centralizer ({t} : Set X) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ 3 → ∀ u : X, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set X) →
        u * t = t * u → u = t) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ht
  subst hg
  let c : X ≃* X := MulAut.conj g⁻¹
  have hc : ∀ w : X, c w = g⁻¹ * w * g := fun w => by simp [c, MulAut.conj_apply]
  have hmap : ∀ F : Subgroup X, F ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set X) →
      F.map c.toMonoidHom ≤ Subgroup.centralizer ({a} : Set X) := by
    rintro F hF _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hF hf)
    show c f * a = a * c f
    rw [hc]
    calc g⁻¹ * f * g * a = g⁻¹ * (f * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * f) * g := by rw [h1]
      _ = a * (g⁻¹ * f * g) := by group
  have hEA : ∀ F : Subgroup X, IsElemAbelian 3 F → IsElemAbelian 3 (F.map c.toMonoidHom) := by
    intro F hF
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      show c x * c y = c y * c x
      rw [← map_mul, ← map_mul, comm_of_elemAbelian' hF hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      show c x ^ 3 = 1
      rw [← map_pow, hF.2 x hx, map_one]
  refine ⟨fun F hF hFE => ?_, fun F hF hFE hF27 u hu huF hut => ?_⟩
  · have := ha _ (hmap F hF) (hEA F hFE)
    rwa [Subgroup.card_map_of_injective c.injective] at this
  · have hcard : Nat.card (F.map c.toMonoidHom) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective c.injective, hF27]
    have hu' : orderOf (c u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
    have huF' : c u ∈ Subgroup.centralizer ((F.map c.toMonoidHom : Subgroup X) : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨f, hf, rfl⟩
      show c f * c u = c u * c f
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 huF) f hf]
    have hut' : c u * a = a * c u := by
      rw [hc]
      calc g⁻¹ * u * g * a = g⁻¹ * (u * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * u) * g := by rw [hut]
        _ = a * (g⁻¹ * u * g) := by group
    have := hb _ (hmap F hF) (hEA F hFE) hcard (c u) hu' huF' hut'
    rw [hc] at this
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = g * a * g⁻¹ := by rw [this]

section Alt

open Equiv Equiv.Perm

theorem not_dvd_card_centralizer_of_even_involution9 {σ : Perm (Fin 9)} (h2 : orderOf σ = 2)
    (hs : Perm.sign σ = 1) :
    ¬ 27 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 9)))) := by
  rw [Perm.nat_card_centralizer]
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [h2]; exact Nat.prime_two)
  rw [h2] at hn
  have hsum := Perm.sum_cycleType_le σ
  have hsign := Perm.sign_of_cycleType σ
  rw [hn] at hsum hsign ⊢
  rw [hs] at hsign
  simp only [Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn4 : n ≤ 3 := by omega
  interval_cases n <;> first | exact absurd hsign (by decide) | decide

end Alt

section Th

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3


@[expose] def ThQCentFact : Prop :=
  ∀ u : J, u ∈ Q → orderOf u = 2 → u ≠ z → ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set J) ⊓ M)

set_option maxRecDepth 100000 in
theorem th_data_a (hQ : ThQCentFact) :
    (∀ F : Subgroup J, F ≤ Subgroup.centralizer ({a} : Set J) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ 3) ∧
    (∀ F : Subgroup J, F ≤ Subgroup.centralizer ({a} : Set J) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ 3 → ∀ u : J, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set J) →
        u * a = a * u → u = a) := by
  haveI : Finite ↥J := Finite.of_equiv _ thEquivJ.toEquiv
  obtain ⟨hCM, -, -, -⟩ := CFSG.Sporadic.ThSchreier.ctuc_Th_full_central_involution_centralizer
  let φ : ↥M →* Equiv.Perm (Fin 9) :=
    (alternatingGroup (Fin 9)).subtype.comp
      (kappa.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf M)))
  have hker : ∀ g : ↥M, φ g = 1 → (g : J) ∈ Q := by
    intro g hg
    have h1 : kappa (QuotientGroup.mk g) = 1 := Subtype.ext hg
    have h2 : (QuotientGroup.mk g : ↥M ⧸ Q.subgroupOf M) = 1 := by
      rw [← map_one kappa.symm, ← h1, MulEquiv.symm_apply_apply]
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff g).1 h2)
  have hQ3 : ∀ q : J, q ∈ Q → q ^ 3 = 1 → q = 1 := by
    intro q hq h3
    have h512 : q ^ 512 = 1 := by
      have := pow_card_eq_one' (G := Q) (x := ⟨q, hq⟩)
      rw [card_Q] at this
      simpa using congrArg Subtype.val this
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h512)
    have : Nat.gcd 3 512 = 1 := by norm_num
    rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hdata : ∀ F : Subgroup J, F ≤ M → IsElemAbelian 3 F →
      IsElemAbelian 3 ((φ.comp (F.subgroupOf M).subtype).range) ∧
        Nat.card ((φ.comp (F.subgroupOf M).subtype).range) = Nat.card F := by
    intro F hFM hF
    have hinj : Function.Injective (φ.comp (F.subgroupOf M).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro w hw
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hw
      have hwQ := hker _ hw
      have hw3 : ((w : ↥M) : J) ^ 3 = 1 := hF.2 _ (Subgroup.mem_subgroupOf.1 w.2)
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subtype.ext (hQ3 _ hwQ hw3))
    refine ⟨isElemAbelian_range _ (fun x y => Subtype.ext (Subtype.ext
      (comm_of_elemAbelian hF (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2))))
      (fun x => Subtype.ext (Subtype.ext (hF.2 _ (Subgroup.mem_subgroupOf.1 x.2)))), ?_⟩
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
  refine ⟨fun F hFC hF => ?_, fun F hFC hF hF27 u hu huF hua => ?_⟩
  · rw [hCM] at hFC
    obtain ⟨hE, hc⟩ := hdata F hFC hF
    rw [← hc]
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltInputs.card_le_pow_div hE
  · rw [hCM] at hFC
    by_contra hne
    have huM : u ∈ M := by
      rw [← hCM]
      exact Subgroup.mem_centralizer_singleton_iff.2 hua
    set ū : Equiv.Perm (Fin 9) := φ ⟨u, huM⟩ with hū
    obtain ⟨-, hc⟩ := hdata F hFC hF
    have hle : (φ.comp (F.subgroupOf M).subtype).range ≤
        Subgroup.centralizer ({ū} : Set (Equiv.Perm (Fin 9))) := by
      rintro _ ⟨w, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hū, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      have hcomm : (F.subgroupOf M).subtype w * (⟨u, huM⟩ : ↥M) =
          (⟨u, huM⟩ : ↥M) * (F.subgroupOf M).subtype w :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.1 huF) _ (Subgroup.mem_subgroupOf.1 w.2))
      rw [hcomm]
    have h27 : 27 ∣ Nat.card (Subgroup.centralizer ({ū} : Set (Equiv.Perm (Fin 9)))) := by
      have h1 := Subgroup.card_dvd_of_le hle
      have h2 : Nat.card ((φ.comp (F.subgroupOf M).subtype).range) = 27 := hc.trans hF27
      rw [h2] at h1
      exact h1
    by_cases hū1 : ū = 1
    ·
      have huQ : u ∈ Q := hker _ hū1
      have huz : u ≠ z := by rw [z_eq_a]; exact hne
      apply hQ u huQ hu huz
      have hFle : F ≤ Subgroup.centralizer ({u} : Set J) ⊓ M := by
        intro f hf
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hFC hf⟩
        exact (Subgroup.mem_centralizer_iff.1 huF) f hf
      have := Subgroup.card_dvd_of_le hFle
      rwa [hF27] at this
    · have hū2 : orderOf ū = 2 := by
        refine orderOf_eq_prime ?_ hū1
        rw [hū, ← map_pow]
        have : (⟨u, huM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by
          have := pow_orderOf_eq_one u
          rwa [hu] at this)
        rw [this, map_one]
      have hūs : Equiv.Perm.sign ū = 1 :=
        Equiv.Perm.mem_alternatingGroup.1 (kappa (QuotientGroup.mk ⟨u, huM⟩)).2
      exact not_dvd_card_centralizer_of_even_involution9 hū2 hūs h27

set_option maxRecDepth 100000 in
theorem th_isConj_a (hTh : Nat.card CFSG.Blueprint.NativeSporadic.Th = 90745943887872000)
    (t : ↥J) (ht : orderOf t = 2) : IsConj a t := by
  have h := CFSG.Sporadic.Th.Max3.th_involutions_conjugate_of_card hTh (thEquivJ.symm t)
    (by rw [MulEquiv.orderOf_eq, ht])
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨thEquivJ g, ?_⟩
  have := congrArg thEquivJ hg
  rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

set_option maxRecDepth 100000 in
theorem twoLocalBound27_J (hQ : ThQCentFact) : TwoLocalBound27 ↥J := by
  haveI : Finite ↥J := Finite.of_equiv _ thEquivJ.toEquiv
  have hTh : Nat.card CFSG.Blueprint.NativeSporadic.Th = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  intro R E hR hR2 hEN hE
  have hd := th_data_a hQ
  exact card_le_of_involution_data
    (fun t ht => (involution_data_of_conj hd.1 hd.2 (th_isConj_a hTh t ht)).1)
    (fun t ht => (involution_data_of_conj hd.1 hd.2 (th_isConj_a hTh t ht)).2) R E hR hR2 hEN hE

set_option maxRecDepth 100000 in
theorem i1016ThFact_of_qCent (hQ : ThQCentFact) : I1016ThFact := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th
  have φ₁ : K ≃* CFSG.Blueprint.NativeSporadic.Carrier .Th := e.trans b.symm
  have hN : TwoLocalBound27 CFSG.Blueprint.NativeSporadic.Th := by
    have hJ := twoLocalBound27_J hQ
    refine twoLocalBound27_of_mulEquiv (G := CFSG.Blueprint.NativeSporadic.Th) (H := ↥J) ?_ hJ
    exact thEquivJ
  have hC : TwoLocalBound27 (CFSG.Blueprint.NativeSporadic.Carrier .Th) := by
    unfold CFSG.Blueprint.NativeSporadic.Carrier
    exact hN
  have hK : TwoLocalBound27 K := twoLocalBound27_of_mulEquiv φ₁ hC
  exact CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    fun R E hR hR2 hEN hE => hK R E hR hR2 hEN hE

end Th

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
