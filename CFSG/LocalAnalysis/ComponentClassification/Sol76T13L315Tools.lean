module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Balanced
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddResidualIn_oddResidualIn (Y : Subgroup G) :
    oddResidualIn (oddResidualIn Y) = oddResidualIn Y :=
  le_antisymm ((closure_le _).mpr fun _ hx => hx.1)
    ((closure_le _).mpr fun _ hx => subset_closure ⟨subset_closure hx, hx.2⟩)

omit [Finite G] in
theorem le_of_le_sup_of_coprime {J W O : Subgroup G} (hJ : oddResidualIn J = J)
    (hOW : O ≤ normalizer (W : Set G)) (hO : Nat.Coprime 2 (Nat.card O)) (hle : J ≤ W ⊔ O) :
    J ≤ W := by
  rw [← hJ]
  refine (closure_le _).mpr ?_
  rintro x ⟨hxJ, k, hk⟩
  have hidx : Nat.Coprime 2 ((O ⊓ W).subgroupOf O).index :=
    Nat.Coprime.coprime_dvd_right (Subgroup.index_dvd_card _) hO
  exact mem_of_mem_sup_of_coprime_index hOW hidx (hle hxJ) hk

omit [Finite G] in
theorem commutator_eq_bot_of_le_centralizer {A P : Subgroup G} (hP : Group.IsPerfect ↥P)
    (h : ⁅A, P⁆ ≤ centralizer (P : Set G)) : ⁅A, P⁆ = ⊥ := by
  rw [commutator_comm] at h ⊢
  exact LocalCores.perfect_double_commutator hP (commutator_eq_bot_iff_le_centralizer.mpr h)

theorem exists_orderOf_eq_two_lift {J Q : Type*} [Group J] [Finite J] [Group Q] {φ : J →* Q}
    (hφ : Function.Surjective φ) (hker : Nat.Coprime 2 (Nat.card φ.ker)) {q : Q}
    (hq : orderOf q = 2) : ∃ j : J, orderOf j = 2 ∧ φ j = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j₀, rfl⟩ := hφ q
  have hn : orderOf j₀ ≠ 0 := (orderOf_pos j₀).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hq2 : φ j₀ ^ 2 = 1 := by rw [← hq, pow_orderOf_eq_one]
  have hqm : φ j₀ ^ m = φ j₀ := by
    obtain ⟨t, rfl⟩ := hm
    rw [pow_succ, pow_mul, hq2, one_pow, one_mul]
  set j₁ := j₀ ^ m with hj₁
  have hφj₁ : φ j₁ = φ j₀ := by rw [hj₁, map_pow, hqm]
  have hj₁2 : j₁ ^ (2 ^ a) = 1 := by
    rw [hj₁, ← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hsq : j₁ ^ 2 = 1 := by
    have hmem : j₁ ^ 2 ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hφj₁, hq2]
    have h1 : orderOf (j₁ ^ 2) ∣ Nat.card φ.ker := Subgroup.orderOf_dvd_natCard _ hmem
    have h2 : orderOf (j₁ ^ 2) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, hj₁2, one_pow])
    have h3 : Nat.Coprime (2 ^ a) (Nat.card φ.ker) := Nat.Coprime.pow_left a hker
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h3) h1
    exact orderOf_eq_one_iff.mp h4
  have hj₁1 : j₁ ≠ 1 := fun h => by
    rw [h, map_one] at hφj₁
    rw [← hφj₁, orderOf_one] at hq
    norm_num at hq
  exact ⟨j₁, orderOf_eq_prime hsq hj₁1, hφj₁⟩

theorem le_of_forall_involution {J L H : Subgroup G} (hJL : J ≤ L)
    (hJsup : J ⊔ oddCoreIn L = L) (hJres : oddResidualIn J = J)
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hnc : ∃ q : ↥L ⧸ pPrimeCore 2 ↥L, orderOf q = 2 ∧ q ∉ center (↥L ⧸ pPrimeCore 2 ↥L))
    (hJH : J ≤ normalizer (H : Set G)) (hinv : ∀ x ∈ J, orderOf x = 2 → x ∈ H) : J ≤ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hJL) with hπ
  have hπs : Function.Surjective π := surjective_mk_comp_inclusion hJL hJsup
  have hoddL : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
  have hπk : Nat.Coprime 2 (Nat.card π.ker) :=
    Nat.coprime_two_left.mpr (odd_card_ker_mk_comp_inclusion hJL (pPrimeCore 2 ↥L) hoddL)
  set W : Subgroup ↥J := H.subgroupOf J with hW
  have hWn : W.Normal := ⟨fun w hw j => by
    rw [hW, mem_subgroupOf] at hw ⊢
    have h1 := (mem_normalizer_iff.mp (hJH j.2) w).mp hw
    simpa using h1⟩
  have hW'n : (W.map π).Normal := Subgroup.Normal.map hWn π hπs
  obtain ⟨q, hq2, hqc⟩ := hnc
  obtain ⟨j, hj2, hjq⟩ := exists_orderOf_eq_two_lift hπs hπk hq2
  have hjH : (j : G) ∈ H := hinv j j.2 (by rw [orderOf_coe]; exact hj2)
  have hqW : q ∈ W.map π := ⟨j, mem_subgroupOf.mpr hjH, hjq⟩
  have htop : W.map π = ⊤ := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hLq
        hW'n.isSubnormal with h | h
    · exact h
    · exact absurd (h hqW) hqc
  have hle : J ≤ H ⊔ (J ⊓ oddCoreIn L) := by
    intro x hx
    have hx' : π ⟨x, hx⟩ ∈ W.map π := htop ▸ mem_top _
    obtain ⟨w, hw, hwx⟩ := hx'
    have hk : w⁻¹ * ⟨x, hx⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwx, inv_mul_cancel]
    have hkO : ((w⁻¹ * ⟨x, hx⟩ : ↥J) : G) ∈ oddCoreIn L := by
      have h1 : π (w⁻¹ * ⟨x, hx⟩) = 1 := hk
      rw [hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have hxe : x = (w : G) * ((w⁻¹ * ⟨x, hx⟩ : ↥J) : G) := by simp
    rw [hxe]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mp hw))
      (mem_sup_right ⟨(w⁻¹ * ⟨x, hx⟩).2, hkO⟩)
  have hodd : Nat.Coprime 2 (Nat.card ↥(J ⊓ oddCoreIn L)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) (coprime_card_oddCoreIn L)
  exact le_of_le_sup_of_coprime hJres (inf_le_left.trans hJH) hodd hle

theorem exists_noncentral_involution_coreQuot (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {H K : Subgroup G} (hKH : IsTwoComponentIn K H)
    (hKs : K ∈ solomonKStar G) :
    ∃ q : ↥K ⧸ pPrimeCore 2 ↥K, orderOf q = 2 ∧ q ∉ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥K ⧸ pPrimeCore 2 ↥K with hQ
  have hQq : IsQuasisimple Q := isQuasisimple_quotient_of_isPComponent hKH.1 hKH.2
  have hcat := catalog_coreQuotient_of_mem_solomonKStar hG hKH hKs
  by_contra hall
  push Not at hall
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have h2 := two_le_pRank_of_mem_solomonKStar hKs
  have := Fintype.ofFinite ↥E
  have h4 : 4 ≤ Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card, hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; omega) (1 : ↥E)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥E))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  have hsq : ∀ w : ↥E, (w : G) ^ 2 = 1 := fun w => hE.2 w w.2
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
  have himg : ∀ w : ↥E, w ≠ 1 → orderOf (π ⟨w, hEK w.2⟩) = 2 := by
    intro w hw
    have hne : π ⟨w, hEK w.2⟩ ≠ 1 := by
      intro h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      have h1 := Subgroup.orderOf_dvd_natCard _ h
      have hw2 : orderOf (⟨w, hEK w.2⟩ : ↥K) = 2 := by
        rw [← orderOf_coe]
        exact orderOf_eq_prime (hsq w) fun h' => hw (Subtype.ext h')
      rw [hw2] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd hodd h1) (by norm_num)
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow]
    have : (⟨w, hEK w.2⟩ : ↥K) ^ 2 = 1 := Subtype.ext (hsq w)
    rw [this, map_one]
  have hinj : π ⟨u, hEK u.2⟩ ≠ π ⟨v, hEK v.2⟩ := by
    intro h
    have h1 : (⟨u * v, hEK (mul_mem u.2 v.2)⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
      have huinv : ((u : G))⁻¹ = u := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hsq u]
      have : (⟨u, hEK u.2⟩ : ↥K)⁻¹ * ⟨v, hEK v.2⟩ = ⟨u * v, hEK (mul_mem u.2 v.2)⟩ :=
        Subtype.ext (by simp [huinv])
      rwa [this] at h
    have huv1 : ((u : G) * v) ≠ 1 := by
      intro h
      apply hvu
      have huinv : ((u : G))⁻¹ = u := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hsq u]
      apply Subtype.ext
      exact (eq_inv_of_mul_eq_one_right h).trans huinv
    have huv2 : ((u : G) * v) ^ 2 = 1 := hsq (u * v)
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    have h3 : orderOf (⟨u * v, hEK (mul_mem u.2 v.2)⟩ : ↥K) = 2 := by
      rw [← orderOf_coe]
      exact orderOf_eq_prime huv2 huv1
    rw [h3] at h2
    exact absurd (Nat.Coprime.eq_one_of_dvd hodd h2) (by norm_num)
  obtain ⟨x, hx2, hxc⟩ := hq.1 Q hQq hcat _ _ (himg u hu) (himg v hv1) hinj
    (hall _ (himg u hu)) (hall _ (himg v hv1))
  exact hxc (hall x hx2)

omit [Finite G] in
theorem elemAbelian_closure_pair {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : Commute a b) : CFSG.Open.IsElemAbelian 2 (closure ({a, b} : Set G)) := by
  have hpair : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcomm := Subgroup.isMulCommutative_closure hpair
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | one => exact one_pow 2
  | mul x y hx hy px py =>
    have hxy : x * y = y * x := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [(Commute.mul_pow hxy 2), px, py, one_mul]
  | inv x hx px => rw [inv_pow, px, inv_one]

theorem exists_elemAbelian_of_involution {K : Subgroup G} (hK : 2 ≤ CFSG.Open.pRank 2 K) {b : G}
    (hbK : b ∈ K) (hb2 : orderOf b = 2) :
    ∃ B : Subgroup G, B ≤ K ∧ CFSG.Open.IsElemAbelian 2 B ∧ 4 ≤ Nat.card B ∧ b ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzK, hz2, hzb, hcomm⟩ : ∃ z ∈ K, orderOf z = 2 ∧ z ≠ b ∧ Commute z b := by
    set b' : ↥K := ⟨b, hbK⟩ with hb'
    have hb'2 : orderOf b' = 2 := by rw [← orderOf_coe]; exact hb2
    have hU2 : IsPGroup 2 (zpowers b') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb'2, pow_one])
    obtain ⟨P, hbP⟩ := hU2.exists_le_sylow
    have hb'P : b' ∈ (P : Subgroup ↥K) := hbP (mem_zpowers b')
    by_cases hcen : (⟨b', hb'P⟩ : ↥(P : Subgroup ↥K)) ∈ center ↥(P : Subgroup ↥K)
    ·
      obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
      set E' : Subgroup ↥K := E.subgroupOf K with hE'
      have hE'2 : IsPGroup 2 E' := by
        rw [IsPGroup.iff_orderOf]
        intro g
        by_cases hg : g = 1
        · exact ⟨0, by rw [hg, orderOf_one, pow_zero]⟩
        · refine ⟨1, ?_⟩
          rw [pow_one]
          refine orderOf_eq_prime ?_ hg
          apply Subtype.ext
          apply Subtype.ext
          simpa using hE.2 _ (mem_subgroupOf.mp g.2)
      obtain ⟨Q, hEQ⟩ := hE'2.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q P
      have hEP : E'.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup ↥K) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        rintro _ ⟨e, he, rfl⟩
        exact ⟨e, hEQ he, rfl⟩
      have hcardE' : Nat.card E' = Nat.card E := by
        rw [hE', ← Subgroup.card_map_of_injective K.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEK]
      have hcardF : 4 ≤ Nat.card (E'.map (MulAut.conj g).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardE', hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) hK
      set F := E'.map (MulAut.conj g).toMonoidHom with hF
      have := Fintype.ofFinite ↥F
      obtain ⟨y, hy1, hyb⟩ : ∃ y : ↥F, (y : ↥K) ≠ 1 ∧ (y : ↥K) ≠ b' := by
        have h3 : 2 < Fintype.card ↥F := by rw [← Nat.card_eq_fintype_card]; omega
        obtain ⟨y₁, -, hy₁⟩ := Finset.exists_mem_ne (s := Finset.univ)
          (by rw [Finset.card_univ]; omega) (1 : ↥F)
        by_cases hbF : b' ∈ F
        · obtain ⟨y₂, hy₂, hy₂b⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥F))
            (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega)
            ⟨b', hbF⟩
          refine ⟨y₂, fun h => Finset.ne_of_mem_erase hy₂ (Subtype.ext h), fun h => hy₂b ?_⟩
          exact Subtype.ext h
        · exact ⟨y₁, fun h => hy₁ (Subtype.ext h), fun h => hbF (h ▸ y₁.2)⟩
      obtain ⟨e, he, hye⟩ := y.2
      have hy2 : (y : ↥K) ^ 2 = 1 := by
        rw [← hye]
        have : e ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ (mem_subgroupOf.mp he))
        rw [← map_pow, this, map_one]
      have hyP : (y : ↥K) ∈ (P : Subgroup ↥K) := hEP y.2
      refine ⟨(y : ↥K), (y : ↥K).2, ?_, fun h => hyb (Subtype.ext h), ?_⟩
      · rw [orderOf_coe]
        exact orderOf_eq_prime hy2 hy1
      · have h1 := (mem_center_iff.mp hcen) ⟨(y : ↥K), hyP⟩
        have h2 := congrArg (fun w : ↥(P : Subgroup ↥K) => ((w : ↥K) : G)) h1
        exact show ((y : ↥K) : G) * b = b * ((y : ↥K) : G) by simpa [hb'] using h2
    ·
      have hP2 : IsPGroup 2 ↥(P : Subgroup ↥K) := P.isPGroup'
      have hb'1 : b' ≠ 1 := fun h => by rw [h, orderOf_one] at hb'2; norm_num at hb'2
      have : Nontrivial ↥(P : Subgroup ↥K) :=
        nontrivial_of_ne ⟨b', hb'P⟩ 1 (fun h => hb'1 (congrArg Subtype.val h))
      have hZ := hP2.center_nontrivial
      have := Fintype.ofFinite ↥(center ↥(P : Subgroup ↥K))
      have h2 : 2 ∣ Fintype.card ↥(center ↥(P : Subgroup ↥K)) := by
        have hZ2 : IsPGroup 2 ↥(center ↥(P : Subgroup ↥K)) := hP2.to_subgroup _
        obtain ⟨n, hn⟩ := hZ2.exists_card_eq
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hn
          have := Finite.one_lt_card_iff_nontrivial.mpr hZ
          omega
        rw [← Nat.card_eq_fintype_card, hn]
        exact dvd_pow_self 2 hn0
      obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card 2 h2
      refine ⟨(((z₀ : ↥(P : Subgroup ↥K)) : ↥K) : G), (((z₀ : ↥(P : Subgroup ↥K)) : ↥K)).2, ?_,
        ?_, ?_⟩
      · rw [orderOf_coe, orderOf_coe, orderOf_coe, hz₀]
      · intro h
        apply hcen
        have : (z₀ : ↥(P : Subgroup ↥K)) = ⟨b', hb'P⟩ := Subtype.ext (Subtype.ext h)
        rw [← this]
        exact z₀.2
      · have h1 := (mem_center_iff.mp z₀.2) ⟨b', hb'P⟩
        have h2 := congrArg (fun w : ↥(P : Subgroup ↥K) => ((w : ↥K) : G)) h1
        exact h2.symm
  have hb2' : b ^ 2 = 1 := by rw [← hb2, pow_orderOf_eq_one]
  have hz2' : z ^ 2 = 1 := by rw [← hz2, pow_orderOf_eq_one]
  refine ⟨closure ({b, z} : Set G), ?_, elemAbelian_closure_pair hb2' hz2' hcomm.symm, ?_,
    subset_closure (Set.mem_insert b _)⟩
  · rw [closure_le]
    rintro x (rfl | rfl)
    · exact hbK
    · exact hzK
  ·
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; norm_num at hb2
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
    have hbinv : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2']
    have hbz1 : b * z ≠ 1 := fun h => hzb (by rw [eq_inv_of_mul_eq_one_right h, hbinv])
    have hbzb : b * z ≠ b := fun h => hz1 (mul_left_cancel (h.trans (mul_one b).symm))
    have hbzz : b * z ≠ z := fun h => hb1 (mul_right_cancel (h.trans (one_mul z).symm))
    set S : Finset G := {1, b, z, b * z} with hS
    have hScard : S.card = 4 := by
      rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm hbzz)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hzb, Ne.symm hbzb⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hb1, Ne.symm hz1, Ne.symm hbz1⟩
    have hsub : (S : Set G) ⊆ (closure ({b, z} : Set G) : Set G) := by
      intro x hx
      simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
      · exact mul_mem (subset_closure (Set.mem_insert _ _))
          (subset_closure (Set.mem_insert_of_mem _ rfl))
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hScard] at h1
    rwa [← Nat.card_coe_set_eq] at h1

end CFSG.ComponentClassification.Sol76T13
