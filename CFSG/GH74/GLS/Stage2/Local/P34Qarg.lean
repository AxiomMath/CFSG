module

public import CFSG.GH74.GLS.Stage2.Local.P34Kind
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

section Proj

variable {Y : Type*} [Group Y] {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
  (hinf : A ⊓ B = ⊥)

include hcomm in
theorem commAB : ∀ (m : ↥A) (n : ↥B), Commute (A.subtype m) (B.subtype n) :=
  fun m n => hcomm m m.2 n n.2

@[expose] def mulAB : ↥A × ↥B →* Y :=
  A.subtype.noncommCoprod B.subtype (commAB hcomm)

include hinf in
theorem mulAB_injective : Function.Injective (mulAB hcomm) := by
  unfold mulAB
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
  rw [Subgroup.range_subtype, Subgroup.range_subtype]
  exact disjoint_iff_inf_le.2 (le_of_eq hinf)

theorem mulAB_apply (a : ↥A) (b : ↥B) : mulAB hcomm (a, b) = (a : Y) * b :=
  MonoidHom.noncommCoprod_apply _ _ _ _

theorem range_mulAB : (mulAB hcomm).range = A ⊔ B := by
  unfold mulAB
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

include hinf in
noncomputable def prodEquiv : ↥A × ↥B ≃* ↥(A ⊔ B) :=
  MulEquiv.ofBijective ((mulAB hcomm).codRestrict (A ⊔ B) (fun x => by
    rw [← range_mulAB hcomm]; exact ⟨x, rfl⟩))
    ⟨fun x y h => mulAB_injective hcomm hinf (congrArg Subtype.val h), fun x => by
      have hx : (x : Y) ∈ (mulAB hcomm).range := by rw [range_mulAB hcomm]; exact x.2
      obtain ⟨p, hp⟩ := hx
      exact ⟨p, Subtype.ext hp⟩⟩

include hinf in
theorem prodEquiv_apply (a : ↥A) (b : ↥B) : ((prodEquiv hcomm hinf (a, b) : ↥(A ⊔ B)) : Y) = a * b := by
  change mulAB hcomm (a, b) = _
  exact mulAB_apply hcomm a b

include hinf in
noncomputable def projB : ↥(A ⊔ B) →* ↥B :=
  (MonoidHom.snd ↥A ↥B).comp (prodEquiv hcomm hinf).symm.toMonoidHom

include hinf in
theorem projB_eq_one_iff {x : Y} (hx : x ∈ A ⊔ B) :
    projB hcomm hinf ⟨x, hx⟩ = 1 ↔ x ∈ A := by
  let e := prodEquiv hcomm hinf
  obtain ⟨p, hp⟩ : ∃ p : ↥A × ↥B, p = e.symm ⟨x, hx⟩ := ⟨_, rfl⟩
  have hxe : e p = ⟨x, hx⟩ := by rw [hp]; exact e.apply_symm_apply _
  have hxab : x = (p.1 : Y) * (p.2 : Y) := by
    have h1 := congrArg Subtype.val hxe
    have h2 := prodEquiv_apply hcomm hinf p.1 p.2
    exact h1.symm.trans h2
  have hproj : projB hcomm hinf ⟨x, hx⟩ = p.2 := by rw [hp]; rfl
  rw [hproj]
  constructor
  · intro h
    rw [hxab, h]
    simp
  · intro hxA
    have hbB : (p.2 : Y) ∈ B := p.2.2
    have hbA : (p.2 : Y) ∈ A := by
      have : (p.2 : Y) = (p.1 : Y)⁻¹ * x := (inv_mul_eq_of_eq_mul hxab).symm
      rw [this]
      exact A.mul_mem (A.inv_mem p.1.2) hxA
    have : (p.2 : Y) ∈ A ⊓ B := ⟨hbA, hbB⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subtype.ext this

end Proj

section QArg

theorem odd_card_of_forall_odd {M : Type*} [Group M] [Finite M] (h : ∀ x : M, Odd (orderOf x)) :
    Odd (Nat.card M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h2 : 2 ∣ Nat.card M := by
    rcases Nat.even_or_odd (Nat.card M) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

variable {Y : Type} [Group Y] [Finite Y]

theorem odd_card_ker {P Q : Type*} [Group P] [Finite P] [Group Q] (f : P →* Q)
    (hodd : ∀ p : P, f p = 1 → Odd (orderOf p)) : ¬ 2 ∣ Nat.card f.ker := by
  have h := odd_card_of_forall_odd (M := ↥f.ker) (fun x => by
    rw [← Subgroup.orderOf_coe]
    exact hodd x.1 x.2)
  intro hd
  exact (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 hd)

theorem q_side {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hB2 : Open.pRank 2 (⊤ : Subgroup ↥B) ≤ 2)
    {P : Subgroup Y} (hP : P ≤ A ⊔ B) {Q : Type} [Group Q] [Finite Q] (f : ↥P →* Q)
    (hf : Function.Surjective f) (hodd : ∀ p : ↥P, f p = 1 → Odd (orderOf p))
    (hA : ∀ p : ↥P, (p : Y) ∈ A → f p = 1) (hQ2 : 3 ≤ Open.pRank 2 (⊤ : Subgroup Q)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let h' : ↥P →* ↥B := (projB hcomm hinf).comp (Subgroup.inclusion hP)
  have hker : ∀ p : ↥P, h' p = 1 → f p = 1 := fun p hp =>
    hA p ((projB_eq_one_iff hcomm hinf (hP p.2)).1 hp)
  have hf1 : ¬ 2 ∣ Nat.card f.ker := odd_card_ker f hodd
  have hh1 : ¬ 2 ∣ Nat.card h'.ker := odd_card_ker h' (fun p hp => hodd p (hker p hp))
  have e1 : Open.pRank 2 (⊤ : Subgroup Q) = Open.pRank 2 (⊤ : Subgroup (↥P ⧸ f.ker)) :=
    (SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm
  have e2 : Open.pRank 2 (⊤ : Subgroup (↥P ⧸ f.ker)) = Open.pRank 2 (⊤ : Subgroup ↥P) :=
    SectionRank.pRank_quotient_eq f.ker hf1
  have e3 : Open.pRank 2 (⊤ : Subgroup (↥P ⧸ h'.ker)) = Open.pRank 2 (⊤ : Subgroup ↥P) :=
    SectionRank.pRank_quotient_eq h'.ker hh1
  have e4 : Open.pRank 2 (⊤ : Subgroup (↥P ⧸ h'.ker)) = Open.pRank 2 (⊤ : Subgroup ↥h'.range) :=
    SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (QuotientGroup.quotientKerEquivRange h')
  have e5 : Open.pRank 2 (⊤ : Subgroup ↥h'.range) ≤ Open.pRank 2 (⊤ : Subgroup ↥B) :=
    SectionRank.pRank_top_le_of_injective (by norm_num) h'.range.subtype h'.range.subtype_injective
  omega

omit [Finite Y] in
theorem normal_subgroupOf_left {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {P : Subgroup Y} (hP : P ≤ A ⊔ B) : (A.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha, b, hb, hg⟩ := exists_mul_of_mem_sup_of_commute' hcomm (hP g.2)
  have hnb : (n : Y) * b = b * n := hcomm n hn b hb
  have : ((g * n * g⁻¹ : ↥P) : Y) = a * (n : Y) * a⁻¹ := by
    have h1 : ((g * n * g⁻¹ : ↥P) : Y) = (g : Y) * n * (g : Y)⁻¹ := rfl
    rw [h1, hg]
    calc a * b * (n : Y) * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
      _ = a * (n : Y) * a⁻¹ := by rw [← hnb]; group
  rw [this]
  exact A.mul_mem (A.mul_mem ha hn) (A.inv_mem ha)

theorem q_argument {A B : Subgroup Y} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hA2 : Open.pRank 2 (⊤ : Subgroup ↥A) ≤ 2) (hB2 : Open.pRank 2 (⊤ : Subgroup ↥B) ≤ 2)
    {P : Subgroup Y} (hP : P ≤ A ⊔ B) {Q : Type} [Group Q] [Finite Q] (f : ↥P →* Q)
    (hf : Function.Surjective f) (hodd : ∀ p : ↥P, f p = 1 → Odd (orderOf p))
    {c : Q} (hc : orderOf c = 2) (hQ1 : ∀ N : Subgroup Q, N.Normal → N ≠ ⊥ → c ∈ N)
    (hQ2 : 3 ≤ Open.pRank 2 (⊤ : Subgroup Q)) : False := by
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  by_cases hNA : ∀ p : ↥P, (p : Y) ∈ A → f p = 1
  · exact q_side hcomm hinf hB2 hP f hf hodd hNA hQ2
  by_cases hNB : ∀ p : ↥P, (p : Y) ∈ B → f p = 1
  · exact q_side hcomm' (by rw [inf_comm]; exact hinf) hA2 (by rwa [sup_comm] at hP) f hf hodd
      hNB hQ2
  push Not at hNA hNB
  obtain ⟨u, huA, hu1⟩ := hNA
  obtain ⟨v, hvB, hv1⟩ := hNB
  have hcomm'' : ∀ a ∈ B, ∀ b ∈ A, a * b = b * a := hcomm'
  have hPBA : P ≤ B ⊔ A := by rwa [sup_comm] at hP
  have hNAn : ((A.subgroupOf P).map f).Normal :=
    Subgroup.Normal.map (normal_subgroupOf_left hcomm hP) f hf
  have hNBn : ((B.subgroupOf P).map f).Normal :=
    Subgroup.Normal.map (normal_subgroupOf_left hcomm'' hPBA) f hf
  have hNAne : (A.subgroupOf P).map f ≠ ⊥ := by
    intro h
    have hmem : f u ∈ (A.subgroupOf P).map f := Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.2 huA)
    rw [h, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  have hNBne : (B.subgroupOf P).map f ≠ ⊥ := by
    intro h
    have hmem : f v ∈ (B.subgroupOf P).map f := Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.2 hvB)
    rw [h, Subgroup.mem_bot] at hmem
    exact hv1 hmem
  obtain ⟨u', hu', hu'c⟩ := Subgroup.mem_map.1 (hQ1 _ hNAn hNAne)
  obtain ⟨v', hv', hv'c⟩ := Subgroup.mem_map.1 (hQ1 _ hNBn hNBne)
  rw [Subgroup.mem_subgroupOf] at hu' hv'
  have hcu : u' * v' = v' * u' := Subtype.ext (hcomm u' hu' v' hv')
  have hw : f (u' * v'⁻¹) = 1 := by rw [map_mul, map_inv, hu'c, hv'c, mul_inv_cancel]
  have hmodd : Odd (orderOf (u' * v'⁻¹)) := hodd _ hw
  set m := orderOf (u' * v'⁻¹) with hm
  have hpow : (u' * v'⁻¹) ^ m = 1 := pow_orderOf_eq_one _
  have hcomm2 : Commute u' v'⁻¹ := (Commute.inv_right (show Commute u' v' from hcu))
  rw [hcomm2.mul_pow, inv_pow, mul_inv_eq_one] at hpow
  have hAm : (u' : Y) ^ m ∈ A := A.pow_mem hu' m
  have hBm : (v' : Y) ^ m ∈ B := B.pow_mem hv' m
  have heq : (u' : Y) ^ m = (v' : Y) ^ m := by
    have := congrArg Subtype.val hpow
    simpa using this
  have hin : (u' : Y) ^ m ∈ A ⊓ B := ⟨hAm, heq ▸ hBm⟩
  rw [hinf, Subgroup.mem_bot] at hin
  have hum : u' ^ m = 1 := Subtype.ext (by simpa using hin)
  have h1 : orderOf u' ∣ m := orderOf_dvd_of_pow_eq_one hum
  have h2 : orderOf c ∣ orderOf u' := by
    rw [← hu'c]
    exact orderOf_map_dvd f u'
  have h3 : orderOf c ∣ m := h2.trans h1
  rw [hc] at h3
  exact absurd (Odd.of_dvd_nat hmodd h3) (by decide)

end QArg

end CFSG.GH74.GLS.Stage2.Local.P34
