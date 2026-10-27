module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open Standing.Setup42

variable {X : Type} [Group X] [Finite X]
variable {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}

theorem exists_ne_comm_of_mulEquiv {G H : Type*} [Group G] [Group H] {P : Subgroup G}
    (e : ↥P ≃* H) {a b : H} (hab : a * b ≠ b * a) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  refine ⟨e.symm a, (e.symm a).2, e.symm b, (e.symm b).2, fun h => hab ?_⟩
  have h1 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
  rw [← map_mul, ← map_mul] at h1
  exact e.symm.injective h1

open DihedralGroup in
theorem dihedral_not_isCyclic {k : ℕ} (hk : 1 ≤ k) : ¬ IsCyclic (DihedralGroup (2 ^ k)) := by
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := DihedralGroup (2 ^ k))
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [nat_card] at hord
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases g with c | c
  · rw [orderOf_r] at hord
    have := Nat.div_le_self (2 ^ k) (Nat.gcd (2 ^ k) c.val)
    omega
  · rw [orderOf_sr] at hord
    omega

namespace Setting46e

theorem orderOf_tBar (hs : Setting46e t L p f S w z V i j) : orderOf (hs.setup.tBar i j) = 2 :=
  orderOf_eq_prime hs.tBar_sq fun h1 => hs.tBar_not_mem_pCore (h1 ▸ one_mem _)

theorem isPGroup_pCore_sup (hs : Setting46e t L p f S w z V i j) :
    IsPGroup 2 ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      zpowers (hs.setup.tBar i j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := pCore_normal
  have hT : IsPGroup 2 (zpowers (hs.setup.tBar i j)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs.orderOf_tBar, pow_one])
  exact (pCore_isPGroup (p := 2) (G := MBar _)).to_sup_of_normal_left hT

theorem index_pCore_subgroupOf (hs : Setting46e t L p f S w z V i j) :
    ((pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subgroupOf
      (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j))).index =
      2 := by
  have : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := pCore_normal
  change (pCore 2 _).relIndex _ = 2
  rw [relIndex_sup_left]
  have hbot : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subgroupOf
      (zpowers (hs.setup.tBar i j)) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hx⟩ hxO
    rcases eq_one_or_eq_of_mem_zpowers hs.orderOf_tBar hx with rfl | rfl
    · exact one_mem _
    · exact absurd hxO hs.tBar_not_mem_pCore
  change ((pCore 2 _).subgroupOf (zpowers (hs.setup.tBar i j))).index = 2
  rw [hbot, index_bot, Nat.card_zpowers, hs.orderOf_tBar]

theorem inf_centralizer_le_pCore_sup (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    {Q : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} (hQ2 : IsPGroup 2 Q)
    (hQK : Q ≤ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
      Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (htQ : hs.setup.tBar i j ∈ Q) (hβQ : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ Q) :
    Q ⊓ centralizer {hs.setup.tBar i j} ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j) := by
  refine (hs.setup.shape_of_le_centralizer_K hFC hKC i j Q hQ2 hQK htQ hβQ).2.trans ?_
  rw [closure_le]
  rintro x (rfl | rfl)
  · exact mem_sup_right (mem_zpowers _)
  · exact mem_sup_left hs.lemma46f.2.2.1.1

theorem exists_not_comm_tBar (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    (hnc : ∃ a ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        zpowers (hs.setup.tBar i j), ∃ b ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        zpowers (hs.setup.tBar i j), a * b ≠ b * a) :
    ∃ y ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j),
      y * hs.setup.tBar i j ≠ hs.setup.tBar i j * y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have hle : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j) ≤
      closure {hs.setup.tBar i j, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} := by
    intro y hy
    exact (hs.setup.shape_of_le_centralizer_K hFC hKC i j _ hs.isPGroup_pCore_sup
      hs.lemma46f.1 (mem_sup_right (mem_zpowers _)) (mem_sup_left hs.lemma46f.2.2.1.1)).2
      ⟨hy, mem_centralizer_singleton_iff.mpr (hcon y hy)⟩
  exact hab (mul_comm_of_mem_closure_pair (mem_center_iff.mp (betaBar_mem_center _) _)
    (hle ha) (hle hb))

theorem isSylowOf_pCore_sup_of (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    (hconj : ∀ x : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      x ∈ normalizer ((pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        zpowers (hs.setup.tBar i j) : Subgroup _) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      ∃ y ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j),
        y * hs.setup.tBar i j * y⁻¹ = x * hs.setup.tBar i j * x⁻¹) :
    IsSylowOf 2 (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        zpowers (hs.setup.tBar i j))
      (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hPR⟩ := exists_isSylowOf_ge hs.isPGroup_pCore_sup hs.lemma46f.1
  have hCR := hs.inf_centralizer_le_pCore_sup hFC hKC hR.isPGroup hR.le
    (hPR (mem_sup_right (mem_zpowers _))) (hPR (mem_sup_left hs.lemma46f.2.2.1.1))
  have heq := eq_of_forall_isConj hR.isPGroup hPR hCR fun x _ hxN => hconj x hxN
  rw [heq]
  exact hR

open DihedralGroup in
theorem of_dihedral (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j)
    (hO : ∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≃*
      DihedralGroup (2 ^ k))) :
    IsSylowOf 2 (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        zpowers (hs.setup.tBar i j))
      (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  obtain ⟨k, hk, ⟨e₀⟩⟩ := hO
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set O := pCore 2 (MBar β) with hOdef
  set tb := hs.setup.tBar i j with htb
  have hOn : O.Normal := pCore_normal
  have hOnc : ¬ IsCyclic ↥O := fun h =>
    dihedral_not_isCyclic hk (isCyclic_of_surjective e₀.toMonoidHom e₀.surjective)
  have hidx := hs.index_pCore_subgroupOf
  have hcardP : Nat.card ↥(O ⊔ zpowers tb) = 2 * Nat.card O := by
    have h1 := Subgroup.relIndex_mul_card (H := O) (K := O ⊔ zpowers tb)
    rw [inf_eq_left.mpr le_sup_left] at h1
    change (O.subgroupOf (O ⊔ zpowers tb)).index * _ = _ at h1
    rw [hidx] at h1
    exact h1.symm
  have hcardO : Nat.card O = 2 * 2 ^ k := by
    rw [Nat.card_congr e₀.toEquiv, nat_card]
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine hs.isSylowOf_pCore_sup_of hFC hKC fun x hxN => ?_
  have htP : tb ∈ O ⊔ zpowers tb := mem_sup_right (mem_zpowers _)
  have ht'P : x * tb * x⁻¹ ∈ O ⊔ zpowers tb := (mem_normalizer_iff.mp hxN tb).mp htP
  have htO : tb ∉ O := hs.tBar_not_mem_pCore
  have ht'O : x * tb * x⁻¹ ∉ O := fun h => htO (by
    have := hOn.conj_mem _ h x⁻¹
    rwa [show x⁻¹ * (x * tb * x⁻¹) * x⁻¹⁻¹ = tb by group] at this)
  have hconjnc : (∃ y ∈ O ⊔ zpowers tb, y * tb ≠ tb * y) →
      ∃ y ∈ O ⊔ zpowers tb, y * (x * tb * x⁻¹) ≠ (x * tb * x⁻¹) * y := by
    rintro ⟨y, hy, hne⟩
    refine ⟨x * y * x⁻¹, (mem_normalizer_iff.mp hxN y).mp hy, fun h => hne ?_⟩
    have h1 : x * (y * tb) * x⁻¹ = x * (tb * y) * x⁻¹ := by
      calc x * (y * tb) * x⁻¹ = x * y * x⁻¹ * (x * tb * x⁻¹) := by group
        _ = x * tb * x⁻¹ * (x * y * x⁻¹) := h
        _ = x * (tb * y) * x⁻¹ := by group
    simpa using h1
  have hsq' : (x * tb * x⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hs.tBar_sq, mul_one, mul_inv_cancel]
  rcases hs.lemma46f.2.1 with h4 | ⟨k', hk', ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exfalso
    rw [hcardP, hcardO] at h4
    omega
  · have hab : (r 1 : DihedralGroup (2 ^ k')) * sr 0 ≠ sr 0 * r 1 := by
      rw [r_mul_sr, sr_mul_r, Ne, sr.injEq, zero_sub, zero_add]
      exact zmod_neg_one_ne_one hk'
    have hnc := hs.exists_not_comm_tBar hFC hKC (exists_ne_comm_of_mulEquiv e hab)
    exact exists_conj_of_dihedral (by omega) e le_sup_left hidx hOnc htP ht'P hs.tBar_sq hsq'
      htO ht'O hnc (hconjnc hnc)
  · have hnc := hs.exists_not_comm_tBar hFC hKC (exists_ne_comm_of_mulEquiv e (sd_r_mul_s_ne hn))
    have hord' : orderOf (x * tb * x⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs.orderOf_tBar]
    exact exists_conj_of_semidihedral hn e htP ht'P hs.orderOf_tBar hord' hnc (hconjnc hnc)

open DihedralGroup in
theorem of_semidihedral (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j)
    (hg : IsLemma46g (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hP : ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      zpowers (hs.setup.tBar i j)) ≃* CFSG.Open.SemidihedralGroup n)) :
    IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ∧
      IsSylowOf 2 (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
          zpowers (hs.setup.tBar i j))
        (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set O := pCore 2 (MBar β) with hOdef
  set tb := hs.setup.tBar i j with htb
  have hOn : O.Normal := pCore_normal
  have htP : tb ∈ O ⊔ zpowers tb := mem_sup_right (mem_zpowers _)
  have htO : tb ∉ O := hs.tBar_not_mem_pCore
  have hnc := hs.exists_not_comm_tBar hFC hKC (exists_ne_comm_of_mulEquiv e (sd_r_mul_s_ne hn))
  refine ⟨?_, hs.isSylowOf_pCore_sup_of hFC hKC fun x hxN => ?_⟩
  · rcases hg.2.2.1 with hcyc | ⟨k, hk, ⟨e₀⟩⟩
    · exact hcyc
    · exfalso
      have : NeZero (2 ^ k) := ⟨by positivity⟩
      have : Fact (1 < 2 ^ k) := ⟨by
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk⟩
      have hinv : ∀ c : ZMod (2 ^ k), orderOf ((e₀.symm (sr c) : ↥O) : MBar β) = 2 := by
        intro c
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_sr]
      have hne : ((e₀.symm (sr 0) : ↥O) : MBar β) ≠ ((e₀.symm (sr 1) : ↥O) : MBar β) := by
        intro h
        have h1 := e₀.symm.injective (Subtype.ext h)
        rw [sr.injEq] at h1
        exact zero_ne_one h1
      have hcen : ∀ {u : MBar β} (hu : u ∈ O ⊔ zpowers tb), orderOf u = 2 →
          (∀ y ∈ O ⊔ zpowers tb, y * u = u * y) → e ⟨u, hu⟩ = CFSG.Semidihedral.z n := by
        intro u hu hu2 hc
        have hmem : e ⟨u, hu⟩ ∈ center (CFSG.Open.SemidihedralGroup n) := by
          rw [mem_center_iff]
          intro c
          obtain ⟨y, rfl⟩ := e.surjective c
          rw [← map_mul, ← map_mul]
          exact congrArg e (Subtype.ext (hc y y.2))
        rw [CFSG.Semidihedral.center_eq_zpowers n hn] at hmem
        rcases eq_one_or_eq_of_mem_zpowers (CFSG.Semidihedral.orderOf_z n (by omega)) hmem with
          h1 | h1
        · exfalso
          have h2 : (⟨u, hu⟩ : ↥(O ⊔ zpowers tb)) = 1 := e.injective (by rw [h1, map_one])
          have h3 : u = 1 := congrArg Subtype.val h2
          rw [h3, orderOf_one] at hu2
          exact absurd hu2 (by norm_num)
        · exact h1
      have hu₀P : ((e₀.symm (sr 0) : ↥O) : MBar β) ∈ O ⊔ zpowers tb :=
        mem_sup_left (e₀.symm (sr 0)).2
      have hu₁P : ((e₀.symm (sr 1) : ↥O) : MBar β) ∈ O ⊔ zpowers tb :=
        mem_sup_left (e₀.symm (sr 1)).2
      by_cases hc₀ : ∀ y ∈ O ⊔ zpowers tb,
          y * ((e₀.symm (sr 0) : ↥O) : MBar β) = ((e₀.symm (sr 0) : ↥O) : MBar β) * y
      · by_cases hc₁ : ∀ y ∈ O ⊔ zpowers tb,
            y * ((e₀.symm (sr 1) : ↥O) : MBar β) = ((e₀.symm (sr 1) : ↥O) : MBar β) * y
        · apply hne
          have h1 := (hcen hu₀P (hinv 0) hc₀).trans (hcen hu₁P (hinv 1) hc₁).symm
          exact congrArg (fun y : ↥(O ⊔ zpowers tb) => (y : MBar β)) (e.injective h1)
        · push Not at hc₁
          obtain ⟨y, hyP, hy⟩ := exists_conj_of_semidihedral hn e hu₁P htP (hinv 1)
            hs.orderOf_tBar hc₁ hnc
          exact htO (hy ▸ hOn.conj_mem _ (e₀.symm (sr 1)).2 y)
      · push Not at hc₀
        obtain ⟨y, hyP, hy⟩ := exists_conj_of_semidihedral hn e hu₀P htP (hinv 0)
          hs.orderOf_tBar hc₀ hnc
        exact htO (hy ▸ hOn.conj_mem _ (e₀.symm (sr 0)).2 y)
  · have ht'P : x * tb * x⁻¹ ∈ O ⊔ zpowers tb := (mem_normalizer_iff.mp hxN tb).mp htP
    have hord' : orderOf (x * tb * x⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hs.orderOf_tBar]
    have hnc' : ∃ y ∈ O ⊔ zpowers tb, y * (x * tb * x⁻¹) ≠ (x * tb * x⁻¹) * y := by
      obtain ⟨y, hy, hne⟩ := hnc
      refine ⟨x * y * x⁻¹, (mem_normalizer_iff.mp hxN y).mp hy, fun h => hne ?_⟩
      have h1 : x * (y * tb) * x⁻¹ = x * (tb * y) * x⁻¹ := by
        calc x * (y * tb) * x⁻¹ = x * y * x⁻¹ * (x * tb * x⁻¹) := by group
          _ = x * tb * x⁻¹ * (x * y * x⁻¹) := h
          _ = x * (tb * y) * x⁻¹ := by group
      simpa using h1
    exact exists_conj_of_semidihedral hn e htP ht'P hs.orderOf_tBar hord' hnc hnc'

end Setting46e

end CFSG.ComponentClassification.HarrisLit
