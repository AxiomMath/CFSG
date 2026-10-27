module

public import CFSG.ClassicalInvolution.AschTight.S19BFus
public import CFSG.ClassicalInvolution.AschTight.S1911FusC
public import CFSG.ClassicalInvolution.AschTight.S19BEnd

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

section OddKernel

theorem isPGroup_zpowers_iff {X : Type} [Group X] (x : X) :
    IsPGroup 2 (Subgroup.zpowers x) ↔ ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h ⟨x, Subgroup.mem_zpowers x⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

variable {H Q : Type} [Group H] [Group Q]

theorem mem_of_map_eq_top (φ : H →* Q) (N : Subgroup H) (hNn : N.Normal) (hN : N.map φ = ⊤)
    (hker : Odd (Nat.card φ.ker)) {g : H} (hg : IsPGroup 2 (Subgroup.zpowers g)) : g ∈ N := by
  obtain ⟨n, hn, hφn⟩ : ∃ n ∈ N, φ n = φ g := by
    have h : φ g ∈ N.map φ := by
      rw [hN]
      trivial
    obtain ⟨n, hn, h'⟩ := h
    exact ⟨n, hn, h'⟩
  have hk : n⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφn, inv_mul_cancel]
  have hko : Odd (orderOf (n⁻¹ * g)) :=
    hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard φ.ker hk)
  have hmk : (QuotientGroup.mk g : H ⧸ N) = QuotientGroup.mk (n⁻¹ * g) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).mpr hn, inv_one,
      one_mul]
  obtain ⟨m, hm⟩ := (isPGroup_zpowers_iff g).mp hg
  have h1 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hm, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk g : H ⧸ N) ∣ orderOf (n⁻¹ * g) := by
    rw [hmk]
    exact orderOf_map_dvd (QuotientGroup.mk' N) _
  have hcop : Nat.Coprime (2 ^ m) (orderOf (n⁻¹ * g)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hko)
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end OddKernel

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W : Subgroup G}

theorem isPerfect_sl2 (h5 : 5 ≤ p ^ f) : Group.IsPerfect SL(2, GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField p f), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField p f))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
    exact ⟨s, hs⟩
  exact CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField p f) (n := 2) le_rfl
    (Or.inr h4)

@[expose] noncomputable def slProjC {F : Type} [Field F]
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (x : G) :
    ↥(K ⊓ Subgroup.centralizer ({x} : Set G)) →* SL(2, F) :=
  (S1911.slProj K e).comp (Subgroup.inclusion inf_le_left)

theorem surjective_slProjC {F : Type} [Field F] (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    {x : G} (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K) :
    Function.Surjective (slProjC e x) := by
  have hBL : Subgroup.zpowers x ≤ centralizerModOdd ⊤ K := Subgroup.zpowers_le.mpr hxK
  have hs := S19B.surjective_mk_inf_centralizer hx2 hBL
  intro b
  obtain ⟨y, hy⟩ := hs (e.symm b)
  have hyx : (y : G) ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x)) y.2.2
  refine ⟨⟨y, y.2.1, hyx⟩, ?_⟩
  have h2 := congrArg e hy
  simp only [MulEquiv.apply_symm_apply] at h2
  exact h2

theorem mem_perfectResidualOf_of_cStar (hd : Sec19Data p f K z S W) {x g : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxK : x ∈ centralizerModOdd ⊤ K) (hgK : g ∈ K)
    (hgx : g ∈ Subgroup.centralizer ({x} : Set G)) (hg2 : IsPGroup 2 (Subgroup.zpowers g)) :
    g ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  obtain ⟨e⟩ := hd.tight.branch.member.nonempty_equiv
  have := isPerfect_sl2 hd.tight.branch.five
  have hsurj := surjective_slProjC e hx2 hxK
  have hmap := finite_perfectResidual_surjects_to_perfect_image (slProjC e x) hsurj
  have hNn : (Helpers.perfectResidual ↥(K ⊓ Subgroup.centralizer ({x} : Set G))).Normal := by
    have := perfectResidual_characteristic (G := ↥(K ⊓ Subgroup.centralizer ({x} : Set G)))
    infer_instance
  have hker : Odd (Nat.card (slProjC e x).ker) := by
    have hle : (slProjC e x).ker.map (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype ≤
        oddCoreOf K := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : S1911.slProj K e (Subgroup.inclusion inf_le_left y) = 1 := hy
      exact (S1911.slProj_eq_one_iff e _).mp hy'
    have hcard : Nat.card ((slProjC e x).ker.map
        (K ⊓ Subgroup.centralizer ({x} : Set G)).subtype) = Nat.card (slProjC e x).ker :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hg2' : IsPGroup 2 (Subgroup.zpowers
      (⟨g, hgK, hgx⟩ : ↥(K ⊓ Subgroup.centralizer ({x} : Set G)))) := by
    obtain ⟨m, hm⟩ := (isPGroup_zpowers_iff g).mp hg2
    exact (isPGroup_zpowers_iff _).mpr ⟨m, Subtype.ext (by simpa using hm)⟩
  exact ⟨_, mem_of_map_eq_top _ _ hNn hmap hker hg2', rfl⟩

variable [IsSimpleGroup G] {L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_conj_eq_t (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t := by
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  obtain ⟨g, hgx, hgz⟩ := S19B.exists_conj_eq_t_of_centralizes hd hxS hxR hxW hxL
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgx, hgz⟩

theorem exists_conj_eq_mul_z (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) :
    ∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = t * z := by
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_t hd hx
  obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hd
  have hrx : r ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1.1.2 r hrR)
  refine ⟨r * g, Subgroup.mul_mem _ hrx hg, ?_⟩
  rw [← hrt, ← hgz]
  group

omit [IsSimpleGroup G] in
theorem exists_sylow_conj (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) {s : G} (hsx : s ∈ Subgroup.centralizer ({x} : Set G))
    (hsz : s ∈ Subgroup.centralizer ({z} : Set G)) (hs2 : IsPGroup 2 (Subgroup.zpowers s)) :
    ∃ S' : Sylow 2 G, Sec19DataT p f K z S' W L t V ∧ x ∈ S19B.sec19BPrime K S' W L ∧
      ∃ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        c * s * c⁻¹ ∈ (S' : Subgroup G) := by
  have hd0 := hd.toSec19Data
  obtain ⟨⟨⟨hxS, hxR⟩, hxW⟩, hxL⟩ := hx
  set H := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) with hH
  have hP₀H : (S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ H :=
    le_inf inf_le_right (inf_le_left.trans hd0.hSz)
  obtain ⟨T, hT, hP₀T⟩ := IsSylow2In.exists_ge (S.isPGroup'.to_le inf_le_left) hP₀H
  obtain ⟨c, hcH, hsc⟩ := Sec7.exists_conj_le_of_isSylow2In hT hs2
    (Subgroup.zpowers_le.mpr ⟨hsx, hsz⟩)
  have hcs : c⁻¹ * s * c ∈ T := by
    have h := mem_conjSub_iff.mp (hsc (Subgroup.mem_zpowers s))
    exact h
  obtain ⟨T', hT', hTT'⟩ := IsSylow2In.exists_ge hT.2.1 (hT.1.trans inf_le_right)
  have hcard : Nat.card T' = Nat.card (S : Subgroup G) :=
    IsSylow2In.natCard_eq hT' (S1916.isSylow2In_of_le S hd0.hSz)
  set S' : Sylow 2 G := Sylow.ofCard T' (by rw [hcard]; exact S.card_eq_multiplicity) with hS'
  have hS'T' : (S' : Subgroup G) = T' := Sylow.coe_ofCard _ _
  have hxS' : ∀ y ∈ (S : Subgroup G), y * x = x * y → y ∈ (S' : Subgroup G) := fun y hy hyx => by
    rw [hS'T']
    exact hTT' (hP₀T ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩)
  have hRS' : (S : Subgroup G) ⊓ K ≤ (S' : Subgroup G) := fun r hr =>
    hxS' r hr.1 (Subgroup.mem_centralizer_iff.mp hxR r hr)
  have hR : (S' : Subgroup G) ⊓ K = (S : Subgroup G) ⊓ K := by
    have hRK := S1911.isSylow2In_inf hd0
    exact hRK.2.2 _ inf_le_right (S'.isPGroup'.to_le inf_le_left) (le_inf hRS' inf_le_right)
  have hWS' : W ≤ (S' : Subgroup G) := fun w hw =>
    hxS' w (hd.hWS hw) (Subgroup.mem_centralizer_iff.mp hxW w hw)
  have hS'z : (S' : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hS'T']
    exact hT'.1
  have hsyl : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S' : Subgroup G) := by
    obtain ⟨Q₀, hQ₀⟩ := hd0.sylow
    exact ⟨Q₀, (le_inf hQ₀ (Subgroup.map_subtype_le _)).trans hRS'⟩
  have hd' : Sec19DataT p f K z S' W L t V :=
    ⟨⟨hd0.tight, hd0.mu, hd0.ih, hd0.cex, hsyl, hS'z, hd0.hW, hWS'⟩, hd.memL, hd.invL, hd.ne,
      hd.memV, hd.leW, hd.memT⟩
  refine ⟨S', hd', ⟨⟨⟨hxS' x hxS rfl, by rw [hR]; exact hxR⟩, hxW⟩, hxL⟩, c⁻¹, H.inv_mem hcH, ?_⟩
  rw [inv_inv, hS'T']
  exact hTT' hcs

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
