module

public import CFSG.GH74.Generic.BProg.B2.T1KleM
public import CFSG.GH74.Generic.BProg.B3.S3Theta52

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

namespace S3T2

variable {G : Type} [Group G]

theorem exists_fixed_in_coset {p : ℕ} [Fact p.Prime] {U V : Subgroup G} (hU : IsPGroup p ↥U)
    (hVp : ¬ p ∣ Nat.card ↥V) (hUV : U ≤ normalizer (V : Set G)) {x : G}
    (hxV : x ∈ normalizer (V : Set G)) (hx : ∀ u ∈ U, u * x * u⁻¹ * x⁻¹ ∈ V) :
    ∃ v ∈ V, ∀ u ∈ U, u * (x * v) * u⁻¹ = x * v := by
  classical
  let T : Type := {y : G // x⁻¹ * y ∈ V}
  have hclosed : ∀ (u : ↥U) (y : T), x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) ∈ V := by
    intro u y
    have hw := hx u u.2
    have hv : (u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hUV u.2) _).1 y.2
    have hxw : x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (V : Set G)).inv_mem hxV)
        _).1 hw
      simpa [mul_assoc] using this
    have : x⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) =
        (x⁻¹ * ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x) *
          ((u : G) * (x⁻¹ * (y : G)) * (u : G)⁻¹) := by
      group
    rw [this]
    exact V.mul_mem hxw hv
  let inst : MulAction ↥U T :=
    { smul := fun u y => ⟨(u : G) * (y : G) * (u : G)⁻¹, hclosed u y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : ↥U) : G) * (y : G) * ((1 : ↥U) : G)⁻¹ = (y : G)
        simp)
      mul_smul := fun u₁ u₂ y => Subtype.ext (by
        show ((u₁ * u₂ : ↥U) : G) * (y : G) * ((u₁ * u₂ : ↥U) : G)⁻¹ =
          (u₁ : G) * ((u₂ : G) * (y : G) * (u₂ : G)⁻¹) * (u₁ : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card ↥V := by
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * (y : G), y.2⟩, fun v => ⟨x * (v : G), by simp⟩,
      fun y => by apply Subtype.ext; simp, fun v => by apply Subtype.ext; simp⟩
  obtain ⟨y, hy⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card T (by rw [hcard]; exact hVp)
  refine ⟨x⁻¹ * (y : G), y.2, fun u hu => ?_⟩
  have h1 : (u : G) * (y : G) * (u : G)⁻¹ = (y : G) := by
    have := congrArg Subtype.val (hy ⟨u, hu⟩)
    exact this
  have : x * (x⁻¹ * (y : G)) = (y : G) := by group
  rw [this]
  exact h1

end S3T2

open S3T2

theorem hKB_proved {G : Type} [Group G] [Finite G] :
    ∀ (x : G) (K A B : Subgroup G), Hyp2 G → IsTwoTerminal x K →
      QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B →
      pRank 2 ↥B = 4 → K ≤ gammaK 2 B 3 := by
  classical
  intro x K A B _ ht h3 hsrc hext hB4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hILo : IsILo 2 x K := ht.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := hILo.1
  obtain ⟨hAB, -, -, hBel, -, -, hBeq⟩ := hext
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h3
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, -⟩ : ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧
      x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 ∧
      (QShape3 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨
        QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) := by
    obtain ⟨-, -, -, hcase⟩ := hsrc
    rcases hcase with ⟨-, h1⟩ | h
    · exact (B1.PilotS3.not_qShape1_of_center_trivial h1 hZ).elim
    · exact h
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := hsrc.2.1
  have hA8 : Nat.card ↥A = 8 := hsrc.2.2.1
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set Γ : Subgroup G := gammaK 2 B 3 with hΓ
  set B₀ : Subgroup G := B ⊓ centralizerSection K (pPrimeCoreOf 2 K) with hB₀
  have hxk : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm
  have hAN : A ≤ normalizer (K : Set G) := by
    rw [hAE]
    refine sup_le (hEK.trans Subgroup.le_normalizer) ?_
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (K : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hxk k hk).symm
  have hBN : B ≤ normalizer (K : Set G) := by
    rw [hBeq]
    exact sup_le hAN fun c hc => hc.2.1
  have hOΓ : pPrimeCoreOf 2 K ≤ Γ := by
    have hBO : B ≤ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) := fun g hg =>
      LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥K)
        (hBN hg)
    refine (B2.le_iSup_centralizer_hyperplanes hBel (by rw [hB4]; norm_num) hBO
      (TwoThin.card_pPrimeCoreOf_odd K)).trans ?_
    refine iSup_le fun Q => iSup_le fun hQB => iSup_le fun hQr => ?_
    have hQr' : 3 ≤ pRank 2 ↥Q := by rw [hB4] at hQr; omega
    have hQγ : normalizer (Q : Set G) ≤ Γ := le_iSup₂_of_le Q hQB (le_iSup_of_le hQr' le_rfl)
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hQγ)
  have hxB : x ∈ B := hAB hxA
  have hB16 : Nat.card ↥B = 16 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hBel, hB4]
    norm_num
  obtain ⟨c, hcB₀, hcA⟩ : ∃ c ∈ B₀, c ∉ A := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ A := by
      rw [hBeq]
      exact sup_le le_rfl hcon
    have := Subgroup.card_le_of_le hle
    rw [hB16, hA8] at this
    omega
  have hcB : c ∈ B := hcB₀.1
  have hc1 : c ≠ 1 := fun h => hcA (h ▸ A.one_mem)
  have hc2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hBsq c hcB) hc1
  have hB₀2 : IsPGroup 2 ↥B₀ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥B).to_le inf_le_left
  have hKO : K ≤ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) := fun k hk => by
    refine Subgroup.mem_normalizer_iff.2 fun n =>
      ⟨fun hn => TwoThin.pPrimeCoreOf_normalized K hk hn, fun hn => ?_⟩
    have := TwoThin.pPrimeCoreOf_normalized K (K.inv_mem hk) hn
    rwa [show k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n by group] at this
  have hCb : ∀ b ∈ E, b ≠ 1 → K ⊓ centralizer ({b} : Set G) ≤ Γ := by
    intro b hbE hb1
    have : CFSG.IsElementaryAbelian 2 ↥E := hEel
    have hbB : b ∈ B := hAB (hEA hbE)
    have hb2 : orderOf b = 2 := B2.ShapeGenS45.orderOf_eq_two_of_mem (B := E) hbE hb1
    have hbx : b ≠ x := fun h => hxE (h ▸ hbE)
    intro k hk
    have hkK : k ∈ K := hk.1
    have hkb : k ∈ centralizer ({b} : Set G) := hk.2
    set V : Subgroup G := centralizer ({b} : Set G) ⊓ pPrimeCoreOf 2 K with hV
    have hVodd : ¬ 2 ∣ Nat.card ↥V := by
      have h1 : Nat.card ↥V ∣ Nat.card ↥(pPrimeCoreOf 2 K) :=
        Subgroup.card_dvd_of_le inf_le_right
      intro h2
      exact (Nat.not_even_iff_odd.mpr (TwoThin.card_pPrimeCoreOf_odd K))
        (even_iff_two_dvd.mpr (h2.trans h1))
    have hNinf : ∀ g : G, g ∈ normalizer (centralizer ({b} : Set G) : Set G) →
        g ∈ normalizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) →
          g ∈ normalizer (V : Set G) := by
      intro g h₁ h₂
      rw [Subgroup.mem_normalizer_iff] at h₁ h₂ ⊢
      intro h
      exact ⟨fun hh => ⟨(h₁ h).1 hh.1, (h₂ h).1 hh.2⟩,
        fun hh => ⟨(h₁ h).2 hh.1, (h₂ h).2 hh.2⟩⟩
    have hB₀V : B₀ ≤ normalizer (V : Set G) := by
      intro u hu
      refine hNinf u (Subgroup.le_normalizer ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hBc u hu.1 b hbB)
      · exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (pPrimeCore 2 ↥K) (hBN hu.1)
    have hkV : k ∈ normalizer (V : Set G) := hNinf k (Subgroup.le_normalizer hkb) (hKO hkK)
    have hx : ∀ u ∈ B₀, u * k * u⁻¹ * k⁻¹ ∈ V := by
      intro u hu
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have hub : u ∈ centralizer ({b} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.2 (hBc u hu.1 b hbB)
        exact mul_mem (mul_mem (mul_mem hub hkb) (inv_mem hub)) (inv_mem hkb)
      · have h1 := hu.2.2.2 k hkK
        have h2 : u * k * u⁻¹ * k⁻¹ = ⁅k, u⁆⁻¹ := by
          rw [commutatorElement_inv, commutatorElement_def]
        rw [h2]
        exact inv_mem h1
    obtain ⟨v, hvV, hfix⟩ := exists_fixed_in_coset hB₀2 hVodd hB₀V hkV hx
    have hvK : v ∈ K := TwoThin.pPrimeCoreOf_le K hvV.2
    set P : Subgroup G := closure ({b, x} : Set G) with hP
    have hPB : P ≤ B :=
      (Subgroup.closure_le B).2 (Set.insert_subset_iff.2 ⟨hbB, Set.singleton_subset_iff.2 hxB⟩)
    have hPA : P ≤ A :=
      (Subgroup.closure_le A).2 (Set.insert_subset_iff.2 ⟨hEA hbE, Set.singleton_subset_iff.2 hxA⟩)
    have hPel : CFSG.IsElementaryAbelian 2 ↥P := Th2Sig6.isElementaryAbelian_of_le hBel hPB
    have hRel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hc2
    have hP2 : 2 ≤ pRank 2 ↥P :=
      C3.Layer1.U1a.two_le_pRank_of_commute (subset_closure (by simp)) (subset_closure (by simp))
        hb2 hx2 (hBc b hbB x hxB) hbx
    have hcd : Th2.CommDisj P (zpowers c) := by
      refine ⟨fun p hp r hr => hBc p (hPB hp) r ((Subgroup.zpowers_le.2 hcB) hr), ?_⟩
      refine eq_bot_iff.2 fun z hz => ?_
      rcases CFSG.GH74.GLS.mem_zpowers_two hc2 hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (hPA (h0 ▸ hz.1)) hcA
    have hr := hcd.pRank_sup hPel hRel le_rfl le_rfl
    rw [Th2.pRank_zpowers_of_orderOf_two hc2] at hr
    set Q : Subgroup G := P ⊔ zpowers c with hQ
    have hQB : Q ≤ B := sup_le hPB (Subgroup.zpowers_le.2 hcB)
    have hQr : 3 ≤ pRank 2 ↥Q := by rw [hr]; omega
    have hkvb : k * v ∈ centralizer ({b} : Set G) := mul_mem hkb hvV.1
    have hQC : Q ≤ centralizer ({k * v} : Set G) := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (Subgroup.zpowers_le.2 ?_)
      · refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 hkvb).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 (hxk (k * v) (mul_mem hkK hvK))
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h1 := hfix c hcB₀
        calc c * (k * v) = c * (k * v) * c⁻¹ * c := by group
          _ = k * v * c := by rw [h1]
    have hkvQ : k * v ∈ centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)
    have hQγ : normalizer (Q : Set G) ≤ Γ := le_iSup₂_of_le Q hQB (le_iSup_of_le hQr le_rfl)
    have hkvΓ : k * v ∈ Γ := hQγ (Subgroup.centralizer_le_normalizer _ hkvQ)
    have hvΓ : v ∈ Γ := hOΓ hvV.2
    have : k = k * v * v⁻¹ := by group
    rw [this]
    exact mul_mem hkvΓ (inv_mem hvΓ)
  have hNormal : (pPrimeCore 2 ↥K).Normal := pPrimeCore_normal
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥K)
  let E' : Subgroup ↥K := E.subgroupOf K
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := IsElementaryAbelian.subgroupOf hEK
  have hE'card : Nat.card ↥E' = 4 := by
    rw [← hE4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hE'p : IsPGroup 2 ↥E' := CFSG.IsElementaryAbelian.isPGroup 2 ↥E'
  have hBel' : CFSG.IsElementaryAbelian 2 ↥(E'.map π) := IsElementaryAbelian.map π
  have hBcard : Nat.card ↥(E'.map π) = 4 :=
    (B2.T1KleM.card_map_mk_of_isPGroup hE'p).trans hE'card
  have hgen := B2.ShapeGenS13.shapeGen_3 _ h3 (E'.map π) hBel' hBcard
  let S : Set (Subgroup ↥K) :=
    {U | ∃ b ∈ E', π b ∉ center (↥K ⧸ pPrimeCore 2 ↥K) ∧ U = zpowers b}
  have hb1 : ∀ b ∈ E', π b ∉ center (↥K ⧸ pPrimeCore 2 ↥K) → (b : G) ≠ 1 := by
    intro b _ hbZ hb
    have hb' : b = 1 := Subtype.ext hb
    exact hbZ (by rw [hb', map_one]; exact one_mem _)
  have hS : ∀ U ∈ S, IsPGroup 2 ↥U := by
    rintro U ⟨b, hb, -, rfl⟩
    exact hE'p.to_le (zpowers_le.2 hb)
  have hM : ∀ U ∈ S, centralizer (U : Set ↥K) ≤ Γ.comap K.subtype := by
    rintro U ⟨b, hb, hbZ, rfl⟩ k hk
    have hbk : (b : G) * k = k * b :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hk b (Subgroup.mem_zpowers b))
    have hbG : (b : G) ∈ E := Subgroup.mem_subgroupOf.1 hb
    exact hCb (b : G) hbG (hb1 b hb hbZ)
      ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 hbk.symm⟩
  have hcov : (⨆ U ∈ S, centralizer ((U.map π : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) :
      Set (↥K ⧸ pPrimeCore 2 ↥K))) = ⊤ := by
    refine top_le_iff.1 (hgen.symm.le.trans ?_)
    refine iSup₂_le fun b hb => ?_
    obtain ⟨⟨b', hb', rfl⟩, hbZ⟩ := hb
    refine le_iSup₂_of_le (zpowers b') ⟨b', hb', hbZ, rfl⟩ ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have htop := B2.T1KleM.eq_top_of_cover (Γ.comap K.subtype)
    (Subgroup.map_le_iff_le_comap.1 hOΓ) S hS hM hcov
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ Γ.comap K.subtype := htop ▸ Subgroup.mem_top _
  exact this

end CFSG.GH74.Generic.BProg.B3
