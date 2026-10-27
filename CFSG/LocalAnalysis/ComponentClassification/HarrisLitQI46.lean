module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQuaternion
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.GH74.GLS.TwoThin.Struct
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSD46A
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.GH74.GLS.TwoThin CFSG.ABGLocalTools
open Standing.Setup42

namespace QI46

theorem quaternion_mul_ne {k : ℕ} (hk : 1 ≤ k) :
    (QuaternionGroup.a 1 : QuaternionGroup (2 ^ k)) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
  intro h
  have h1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = 0 := by
    have h3 : ((2 : ℕ) : ZMod (2 * 2 ^ k)) = (0 + 1) - (0 - 1) := by
      push_cast
      ring
    rw [h3, ← h1, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h4 := Nat.le_of_dvd (by norm_num) h2
  have h5 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  omega

theorem quaternion_involution_eq {k : ℕ} {x y : QuaternionGroup (2 ^ k)} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : x = y := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  rw [quaternionGroup_eq_a_of_orderOf_eq_two hx, quaternionGroup_eq_a_of_orderOf_eq_two hy]

theorem not_quaternion_of_le_dihedral {G : Type*} [Group G] {P N : Subgroup G} (hNP : N ≤ P)
    {m : ℕ} (hm : 1 ≤ m) (eP : ↥P ≃* DihedralGroup (2 ^ m)) {k : ℕ} (hk : 1 ≤ k)
    (eN : ↥N ≃* QuaternionGroup (2 ^ k)) : False := by
  set H := (N.subgroupOf P).map eP.toMonoidHom with hH
  have eH : ↥H ≃* QuaternionGroup (2 ^ k) :=
    ((N.subgroupOf P).equivMapOfInjective _ eP.injective).symm.trans
      ((subgroupOfEquivOfLe hNP).trans eN)
  rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm H with hc |
    ⟨j, hj, ⟨eD⟩⟩
  · let _ : CommGroup ↥H := IsCyclic.commGroup
    apply quaternion_mul_ne hk
    apply eH.symm.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · have : Fact (1 < 2 ^ j) := ⟨Nat.one_lt_two_pow (by omega)⟩
    have hne : (DihedralGroup.sr 0 : DihedralGroup (2 ^ j)) ≠ DihedralGroup.sr 1 :=
      fun h => zero_ne_one (DihedralGroup.sr.inj h)
    apply hne
    apply (eD.symm.trans eH).injective
    exact quaternion_involution_eq
      (by rw [MulEquiv.orderOf_eq]; exact DihedralGroup.orderOf_sr 0)
      (by rw [MulEquiv.orderOf_eq]; exact DihedralGroup.orderOf_sr 1)

theorem eq_of_mem_center_of_semidihedral {G : Type*} [Group G] {P : Subgroup G} {n : ℕ}
    (hn : 4 ≤ n) (eP : ↥P ≃* Open.SemidihedralGroup n) {x y : G} (hxP : x ∈ P) (hyP : y ∈ P)
    (hx : x ∈ center G) (hy : y ∈ center G) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have key : ∀ v (hvP : v ∈ P), v ∈ center G → v ≠ 1 →
      eP ⟨v, hvP⟩ = CFSG.Semidihedral.z n := by
    intro v hvP hv hv1
    have hc : eP ⟨v, hvP⟩ ∈ center (Open.SemidihedralGroup n) := by
      rw [mem_center_iff]
      intro u
      obtain ⟨u', rfl⟩ := eP.surjective u
      rw [← map_mul, ← map_mul]
      exact congrArg eP (Subtype.ext (mem_center_iff.mp hv u'))
    rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hc
    rcases SD46.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two
      (CFSG.Semidihedral.orderOf_z n (by omega)) hc with h | h
    · exfalso
      apply hv1
      have h1 : (⟨v, hvP⟩ : ↥P) = 1 := eP.injective (h.trans (map_one eP).symm)
      exact congrArg Subtype.val h1
    · exact h
  have h := (key x hxP hx hx1).trans (key y hyP hy hy1).symm
  exact congrArg Subtype.val (eP.injective h)

end QI46

theorem harris46Quaternion_of_classical
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hCI : GSLit.ClassicalInvolutionInput) : Harris46QuaternionInput := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j' Nb hNb k hk
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  set β := w ^ (orderOf w / 2) * t ^ i' * z ^ j' with hβ
  set M := centralizer ({β} : Set X) with hM
  have hβ2' : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i' j')
  have hb1 : betaBar β ≠ 1 := hs.setup.betaBar_ne_one i' j'
  have hbZ := betaBar_mem_center β
  set b' : ↥M := ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ with hb'
  have hb'2 : b' ^ 2 = 1 := Subtype.ext hβ2'
  have hb2 : orderOf (betaBar β) = 2 := by
    refine orderOf_eq_prime ?_ hb1
    rw [betaBar, ← QuotientGroup.mk_pow]
    rw [show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) ^ 2 = 1 from hb'2,
      QuotientGroup.mk_one]
  have hNbcard : Nat.card ↥Nb = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, pow_add]
    ring
  have huniq : ∀ x ∈ Nb, ∀ y ∈ Nb, orderOf x = 2 → orderOf y = 2 → x = y := by
    intro x hx y hy hx2 hy2
    have h := QI46.quaternion_involution_eq (x := e ⟨x, hx⟩) (y := e ⟨y, hy⟩)
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2])
      (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2])
    exact congrArg Subtype.val (e.injective h)
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥Nb) 2
    (by rw [hNbcard]; exact dvd_pow_self 2 (by omega))
  have hw₀2 : orderOf (w₀ : MBar β) = 2 := by rw [Subgroup.orderOf_coe]; exact hw₀
  have hw₀1 : (w₀ : MBar β) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hw₀2
    omega
  have hw₀Z : (w₀ : MBar β) ∈ center (MBar β) := by
    rw [mem_center_iff]
    intro g
    have hc : g * (w₀ : MBar β) * g⁻¹ ∈ Nb := hNb.conj_mem _ w₀.2 g
    have hc2 : orderOf (g * (w₀ : MBar β) * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw₀2]
    have h := huniq _ hc _ w₀.2 hc2 hw₀2
    calc g * (w₀ : MBar β) = g * (w₀ : MBar β) * g⁻¹ * g := by group
      _ = (w₀ : MBar β) * g := by rw [h]
  obtain ⟨-, hP, hβO, -⟩ := hs.setup.lemma46f hnonab hK hSch hFC hKC i' j'
  have hNbO : Nb ≤ pCore 2 (MBar β) := le_sSup ⟨hNb, IsPGroup.of_card hNbcard⟩
  have hNbP : Nb ≤ pCore 2 (MBar β) ⊔ zpowers (hs.setup.tBar i' j') := hNbO.trans le_sup_left
  have hβP : betaBar β ∈ pCore 2 (MBar β) ⊔ zpowers (hs.setup.tBar i' j') :=
    mem_sup_left (mem_inf.mp hβO).1
  have hbw : betaBar β = w₀ := by
    rcases hP with h4 | ⟨m, hm, ⟨eP⟩⟩ | ⟨n, hn, ⟨eP⟩⟩
    · exfalso
      have h1 := Subgroup.card_dvd_of_le hNbP
      rw [h4, hNbcard] at h1
      have h2 := Nat.le_of_dvd (by norm_num) h1
      have h3 : 2 ^ 3 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact (QI46.not_quaternion_of_le_dihedral hNbP (by omega : 1 ≤ m) eP hk e).elim
    · exact QI46.eq_of_mem_center_of_semidihedral hn eP hβP (hNbP w₀.2) hbZ hw₀Z hb1 hw₀1
  have hbNb : betaBar β ∈ Nb := hbw ▸ w₀.2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set J' : Subgroup ↥M := Nb.comap π with hJ'
  set J₀ : Subgroup X := J'.map M.subtype with hJ₀
  have hJ₀M : J₀ ≤ M := map_subtype_le _
  have hJ'eq : J₀.subgroupOf M = J' := comap_map_eq_self_of_injective M.subtype_injective J'
  have hJ₀n : (J₀.subgroupOf M).Normal := by
    rw [hJ'eq]
    exact hNb.comap π
  have hβJ₀ : β ∈ J₀ := ⟨b', hbNb, rfl⟩
  have hb'Z : ∀ y : ↥M, y * b' = b' * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.2)
  have hOodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) := odd_card_pPrimeCore _
  have hinv : ∀ y ∈ J₀, orderOf y = 2 → y = β := by
    rintro _ ⟨y', hy', rfl⟩ hy2
    have hy2' : y' ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      have h := pow_orderOf_eq_one (M.subtype y')
      rwa [hy2] at h
    by_cases hy1 : π y' = 1
    · exfalso
      have hO : y' ∈ pPrimeCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp hy1
      have h1 := SD46.eq_one_of_mem_of_odd hOodd hO hy2'
      rw [h1, map_one, orderOf_one] at hy2
      omega
    · have hyord : orderOf (π y') = 2 :=
        orderOf_eq_prime (by rw [← map_pow, hy2', map_one]) hy1
      have hyb : π y' = betaBar β := huniq _ hy' _ hbNb hyord hb2
      have hk' : y'⁻¹ * b' ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp hyb
      have hk2 : (y'⁻¹ * b') ^ 2 = 1 := by
        rw [(show Commute y'⁻¹ b' from hb'Z y'⁻¹).mul_pow, inv_pow, hy2', inv_one, one_mul, hb'2]
      have h1 := SD46.eq_one_of_mem_of_odd hOodd hk' hk2
      rw [inv_mul_eq_one.mp h1]
      rfl
  have htight : Open.classicalInvolutionTightlyEmbedded J₀ := by
    intro g hg
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(J₀ ⊓ J₀.map (MulAut.conj g).toMonoidHom)) 2 (even_iff_two_dvd.mp hev)
    have hx2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hx1 : (x : X) = β := hinv x (mem_inf.mp x.2).1 hx2
    obtain ⟨y, hyJ, hyx⟩ := (mem_inf.mp x.2).2
    have hy2 : orderOf y = 2 := by
      rw [← MulEquiv.orderOf_eq (MulAut.conj g) y]
      exact (congrArg orderOf hyx).trans hx2
    have hyβ : y = β := hinv y hyJ hy2
    have hgβ : g * β * g⁻¹ = β := by
      have h := hyx
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hyβ] at h
      rw [h, hx1]
    have hgM : g ∈ M := mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgβ)
    apply hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hJ₀n.conj_mem ⟨h, hJ₀M hh⟩ hh ⟨g, hgM⟩
    · intro hh
      have h1 := hJ₀n.conj_mem ⟨g * h * g⁻¹, hJ₀M hh⟩ hh ⟨g⁻¹, inv_mem hgM⟩
      rw [mem_subgroupOf] at h1
      have h2 : ((⟨g⁻¹, inv_mem hgM⟩ * ⟨g * h * g⁻¹, hJ₀M hh⟩ * ⟨g⁻¹, inv_mem hgM⟩⁻¹ : ↥M) : X)
          = h := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rwa [h2] at h1
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥J₀) := inferInstance
  set U : Subgroup ↥M := (T : Subgroup ↥J₀).map (Subgroup.inclusion hJ₀M) with hU
  have hUp : IsPGroup 2 ↥U := T.isPGroup'.map _
  obtain ⟨eU⟩ := nonempty_mulEquiv_map_mk hUp
  have hUle : U.map π ≤ Nb := by
    rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
    obtain ⟨y', hy', hy'eq⟩ := u.2
    have h1 : Subgroup.inclusion hJ₀M u = y' := Subtype.ext hy'eq.symm
    rw [h1]
    exact hy'
  have hJ₀card : 2 ^ (k + 2) ∣ Nat.card ↥J₀ := by
    rw [← hNbcard]
    have h1 : J'.map π = Nb := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Nb
    have h2 := Subgroup.card_map_dvd J' π
    rw [h1] at h2
    rw [hJ₀, card_map_of_injective M.subtype_injective]
    exact h2
  have hTcard : 2 ^ (k + 2) ≤ Nat.card ↥(T : Subgroup ↥J₀) :=
    Nat.le_of_dvd Nat.card_pos (T.pow_dvd_card_of_pow_dvd_card hJ₀card)
  have hUcard : Nat.card ↥(U.map π) = Nat.card ↥(T : Subgroup ↥J₀) := by
    rw [← Nat.card_congr eU.toEquiv, hU,
      card_map_of_injective (Subgroup.inclusion_injective hJ₀M)]
  have hUeq : U.map π = Nb := eq_of_le_of_card_ge hUle (by rw [hNbcard, hUcard]; exact hTcard)
  have eT : ↥(T : Subgroup ↥J₀) ≃* QuaternionGroup (2 ^ k) :=
    (((T : Subgroup ↥J₀).equivMapOfInjective _ (Subgroup.inclusion_injective hJ₀M)).trans
      eU).trans ((MulEquiv.subgroupCongr hUeq).trans e)
  have hsub : Open.IsSubnormal J₀ (centralizer ({β} : Set X)) :=
    Open.IsSubnormal.step hJ₀M hJ₀n (Open.IsSubnormal.refl _)
  have hβord : orderOf β = 2 := by
    refine orderOf_eq_prime hβ2' fun h1 => hb1 ?_
    rw [betaBar, show (⟨β, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥M) = 1 from Subtype.ext h1,
      QuotientGroup.mk_one]
  let eF : Open.genFittingFStar X ≃* X :=
    (MulEquiv.subgroupCongr (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  rcases (hCI X hFnonab β hβord J₀ hβJ₀ hsub T
      ⟨k + 2, by omega, by rw [Nat.add_sub_cancel]; exact ⟨eT⟩⟩).2 htight with h | h | h
  · exact hcat (catalog_of_oddLieType ((ClassicalInvolution.oddLieType_congr eF).1 h))
  · exact hcat (.inr (.inr (.inr (.inr ⟨.M11, (ClassicalInvolution.isSporadic_congr eF).1 h⟩))))
  · exact hcat (.inr (.inr (.inr (.inr ⟨.M12, (ClassicalInvolution.isSporadic_congr eF).1 h⟩))))

end CFSG.ComponentClassification.HarrisLit
