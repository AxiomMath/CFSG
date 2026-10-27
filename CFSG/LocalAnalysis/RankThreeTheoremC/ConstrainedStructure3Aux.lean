module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial
import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.PreuniquenessRankFour.Helpers

section CyclicCoprime

theorem zpow_pow_comm3 {X : Type*} [Group X] (c : X) (k : ℤ) (p : ℕ) :
    (c ^ k) ^ p = (c ^ p) ^ k := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem conj_eq_of_coprime_of_zpowers {X : Type*} [Group X] {p m : ℕ} (hm : p.Coprime m) (d : X)
    (hd : d ^ m = 1) :
    ∀ (n : ℕ) (c : X), c ^ (p ^ n) = 1 → d * c * d⁻¹ ∈ Subgroup.zpowers c →
      (∀ y ∈ Subgroup.zpowers c, y ^ p = 1 → d * y * d⁻¹ = y) → d * c * d⁻¹ = c := by
  intro n
  induction n with
  | zero =>
    intro c hc _ _
    have : c = 1 := by simpa using hc
    simp [this]
  | succ n ih =>
    intro c hc hcl hΩ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcl
    have hc' : (c ^ p) ^ (p ^ n) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hc
    have hcp_mem : c ^ p ∈ Subgroup.zpowers c := Subgroup.pow_mem _ (Subgroup.mem_zpowers c) p
    have hconj_pow : d * c ^ p * d⁻¹ = (c ^ p) ^ k := by
      rw [← conj_pow, ← hk, zpow_pow_comm3]
    have hcl' : d * c ^ p * d⁻¹ ∈ Subgroup.zpowers (c ^ p) := by
      rw [hconj_pow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    have hΩ' : ∀ y ∈ Subgroup.zpowers (c ^ p), y ^ p = 1 → d * y * d⁻¹ = y := by
      intro y hy hyp
      exact hΩ y ((Subgroup.zpowers_le.mpr hcp_mem) hy) hyp
    have hIH : (c ^ p) ^ k = c ^ p := by
      rw [← hconj_pow]
      exact ih (c ^ p) hc' hcl' hΩ'
    set w : X := c ^ k * c⁻¹ with hw
    have hwmem : w ∈ Subgroup.zpowers c :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k)
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    have hwp : w ^ p = 1 := by
      have hcomm : Commute (c ^ k) c⁻¹ := ((Commute.refl c).zpow_left k).inv_right
      rw [hw, hcomm.mul_pow, inv_pow, zpow_pow_comm3, hIH, mul_inv_cancel]
    have hwd : d * w * d⁻¹ = w := hΩ w hwmem hwp
    have hdc : d * c * d⁻¹ = w * c := by
      rw [← hk, hw, inv_mul_cancel_right]
    have hpow : ∀ j : ℕ, d ^ j * c * (d ^ j)⁻¹ = w ^ j * c := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have : d ^ (j + 1) * c * (d ^ (j + 1))⁻¹ = d * (d ^ j * c * (d ^ j)⁻¹) * d⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
        rw [this, ihj, pow_succ, show d * (w ^ j * c) * d⁻¹ = (d * w * d⁻¹) ^ j * (d * c * d⁻¹) by
          rw [conj_pow, mul_assoc, mul_assoc]; group, hwd, hdc]
        group
    have hwm : w ^ m = 1 := by
      have h1 := hpow m
      rw [hd, inv_one, one_mul, mul_one] at h1
      exact (mul_eq_right.mp h1.symm)
    have hw1 : w = 1 := by
      have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwp
      have h2 : orderOf w ∣ m := orderOf_dvd_of_pow_eq_one hwm
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hm ▸ Nat.dvd_gcd h1 h2))
    rw [hdc, hw1, one_mul]

end CyclicCoprime


section Center

variable {X : Type*} [Group X] {E : Subgroup X} {z : X}

theorem inf_centralizer_eq_of_center_map
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) :
    E ⊓ Subgroup.centralizer (E : Set X) = Subgroup.zpowers z := by
  rw [← hZE]
  ext x
  constructor
  · rintro ⟨hxE, hxC⟩
    refine ⟨⟨x, hxE⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨h, hh⟩)

theorem normal_zpowers_of_center_map [E.Normal]
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) :
    (Subgroup.zpowers z).Normal := by
  rw [← hZE]
  constructor
  rintro _ ⟨c, hc, rfl⟩ g
  refine ⟨⟨g * c * g⁻¹, ‹E.Normal›.conj_mem _ c.2 g⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩
  apply Subtype.ext
  show (u : X) * (g * c * g⁻¹) = (g * c * g⁻¹) * u
  have hu : g⁻¹ * u * g ∈ E := by simpa using ‹E.Normal›.conj_mem u u.2 g⁻¹
  have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨g⁻¹ * u * g, hu⟩)
  have h2 : g⁻¹ * u * g * c = c * (g⁻¹ * u * g) := h1
  calc (u : X) * (g * c * g⁻¹) = g * (g⁻¹ * u * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by rw [h2]
    _ = (g * c * g⁻¹) * u := by group

end Center

section Order

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem exists_isElemAbelian_card_sq_of_card_cube {E : Subgroup X} (hcard : Nat.card E = p ^ 3)
    (hexp : ∀ x ∈ E, x ^ p = 1) : ∃ B ≤ E, IsElemAbelian p B ∧ Nat.card B = p ^ 2 := by
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hcard]; exact pow_dvd_pow p (by norm_num))
  have hcomm : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq hB
  have hB' : IsElemAbelian p B := ⟨hcomm, fun x _ => Subtype.ext (by
    rw [Subgroup.coe_pow]; exact hexp x x.2)⟩
  refine ⟨B.map E.subtype, Subgroup.map_subtype_le B, elementary_abelian_map p hB' E.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hB]

end Order

section Product

variable {X : Type*} [Group X]

theorem exists_mul_eq_of_mem_sup_normal {E H : Subgroup X} [E.Normal] {x : X}
    (hx : x ∈ E ⊔ H) : ∃ g ∈ E, ∃ h ∈ H, g * h = x := by
  exact Subgroup.mem_sup_of_normal_left.mp hx

theorem eq_sup_inf_of_le_sup3 {E Q H : Subgroup X} [E.Normal] (hEQ : E ≤ Q) (hQ : Q ≤ E ⊔ H) :
    Q = E ⊔ (Q ⊓ H) := by
  refine le_antisymm (fun q hq => ?_) (sup_le hEQ inf_le_left)
  obtain ⟨g, hg, h, hh, rfl⟩ := exists_mul_eq_of_mem_sup_normal (hQ hq)
  refine Subgroup.mul_mem_sup hg ⟨?_, hh⟩
  have := Q.mul_mem (Q.inv_mem (hEQ hg)) hq
  rwa [inv_mul_cancel_left] at this

theorem inf_centralizer_le_of_isCyclic3 {E Q R : Subgroup X} [E.Normal] (hEQ : E ≤ Q) (hQR : Q ≤ R)
    (hQE : Q ≤ E ⊔ Subgroup.centralizer (E : Set X))
    (hcyc : IsCyclic (R ⊓ Subgroup.centralizer (E : Set X) : Subgroup X))
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) :
    R ⊓ Subgroup.centralizer (E : Set X) ≤ Q := by
  rintro c ⟨hcR, hcE⟩
  refine hQc (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
  have hq' := eq_sup_inf_of_le_sup3 hEQ hQE ▸ hq
  obtain ⟨g, hg, d, hd, rfl⟩ := exists_mul_eq_of_mem_sup_normal hq'
  have hdc : d * c = c * d := by
    let _ : CommGroup (R ⊓ Subgroup.centralizer (E : Set X) : Subgroup X) := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨d, hQR hd.1, hd.2⟩ : ↥(R ⊓ Subgroup.centralizer
      (E : Set X))) ⟨c, hcR, hcE⟩)
  have hgc : g * c = c * g := (Subgroup.mem_centralizer_iff.mp hcE g hg)
  calc g * d * c = g * (d * c) := by group
    _ = g * (c * d) := by rw [hdc]
    _ = (g * c) * d := by group
    _ = (c * g) * d := by rw [hgc]
    _ = c * (g * d) := by group

end Product

section Inner

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem mem_sup_centralizer_of_commutator_mem {E : Subgroup X} [E.Normal]
    (hcard : Nat.card E = p ^ 3) (hnc : ∃ a b : E, a * b ≠ b * a) {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) {x : X}
    (hx : ∀ u ∈ E, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers z) :
    x ∈ E ⊔ Subgroup.centralizer (E : Set X) := by
  have hzn : (Subgroup.zpowers z).Normal := normal_zpowers_of_center_map hZE
  obtain ⟨-, -, -, -, -, -, hinner⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (S := E) hcard hnc
  obtain ⟨g, hg⟩ := hinner (MulAut.conjNormal x) fun u => by
    have h1 := hzn.conj_mem _ (hx u u.2) (u : X)⁻¹
    have h2 : (u : X)⁻¹ * (x * u * x⁻¹ * (u : X)⁻¹) * ((u : X)⁻¹)⁻¹ =
        ((u⁻¹ * MulAut.conjNormal x u : E) : X) := by
      rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
      group
    rw [h2, ← hZE] at h1
    obtain ⟨c, hc, hcu⟩ := h1
    have : c = u⁻¹ * MulAut.conjNormal x u := Subtype.ext hcu
    rwa [← this]
  have hxg : ∀ u : E, x * u * x⁻¹ = (g : X) * u * (g : X)⁻¹ := fun u => by
    have := congrArg (fun a : MulAut E => ((a u : E) : X)) hg
    simpa [MulAut.conjNormal_apply] using this
  have hcent : (g : X)⁻¹ * x ∈ Subgroup.centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h3 := hxg ⟨u, hu⟩
    have h4 : x * u = (g : X) * u * (g : X)⁻¹ * x := by
      rw [← h3]; group
    calc u * ((g : X)⁻¹ * x) = (g : X)⁻¹ * ((g : X) * u * (g : X)⁻¹ * x) := by group
      _ = (g : X)⁻¹ * (x * u) := by rw [h4]
      _ = ((g : X)⁻¹ * x) * u := by group
  have : x = (g : X) * ((g : X)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup g.2 hcent

end Inner

section Trivial

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem commutator_mem_zpowers_of_normal_pGroup {E N L : Subgroup X} [E.Normal] [N.Normal]
    (hN : IsPGroup p N) (hEN : E ≤ N) (hcard : Nat.card E = p ^ 3) {z : X}
    (hZE : (Subgroup.center E).map E.subtype = Subgroup.zpowers z) (hzp : orderOf z = p)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set X))).map (centerQuotientAction E e)) :
    ∀ q ∈ N, ∀ u ∈ E, q * u * q⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
  have hp := (Fact.out : p.Prime)
  have : (Subgroup.zpowers z).Normal := normal_zpowers_of_center_map hZE
  set mk : X →* X ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z) with hmk
  have hker : mk.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  have hmk_surj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have : (N.map mk).Normal := Subgroup.Normal.map ‹N.Normal› mk hmk_surj
  have : (E.map mk).Normal := Subgroup.Normal.map ‹E.Normal› mk hmk_surj
  have hNp : IsPGroup p (N.map mk) := hN.map mk
  have hEne : E.map mk ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, hker] at hbot
    have := Subgroup.card_le_of_le hbot
    rw [hcard, Nat.card_zpowers, hzp] at this
    have h3 : p ^ 3 = p * p ^ 2 := by ring
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith [pow_pos hp.pos 2]
  obtain ⟨w, hwE, hwp, hwc⟩ := exists_orderOf_eq_prime_commute hNp
    (Subgroup.map_mono hEN) (by rw [Subgroup.normalizer_eq_top]; exact le_top) hEne
  obtain ⟨u, hu, rfl⟩ := hwE
  have huz : u ∉ Subgroup.zpowers z := by
    intro huz
    rw [← hker, MonoidHom.mem_ker] at huz
    rw [huz, orderOf_one] at hwp
    exact hp.one_lt.ne hwp
  let Y : Subgroup X := (Subgroup.centralizer ((N.map mk : Subgroup (X ⧸ Subgroup.zpowers z)) :
    Set (X ⧸ Subgroup.zpowers z))).comap mk
  have : Y.Normal := inferInstance
  have huY : u ∈ E ⊓ Y := ⟨hu, fun r hr => (hwc r hr).eq⟩
  have hzY : Subgroup.zpowers z ≤ Y := by
    intro x hx
    have hx1 : mk x = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hx
    exact (show mk x ∈ Subgroup.centralizer ((N.map mk : Subgroup (X ⧸ Subgroup.zpowers z)) :
      Set (X ⧸ Subgroup.zpowers z)) by rw [hx1]; exact Subgroup.one_mem _)
  rcases inf_le_map_center_or_le_sup_of_normal (E := E) (L := L) (Y := Y) e hSL with h1 | h1
  · exact absurd (hZE ▸ h1 huY) huz
  · have hEY : E ≤ Y := h1.trans (sup_le le_rfl (hZE ▸ hzY))
    intro q hq u' hu'
    have hc := Subgroup.mem_centralizer_iff.mp (hEY hu') (mk q) ⟨q, hq, rfl⟩
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc]
    group

end Trivial


section Burnside

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem isPGroup_centralizer_of_isCyclic {E Q C : Subgroup X} [E.Normal] [Q.Normal]
    (hQp : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    (hQC : Q ⊓ Subgroup.centralizer (E : Set X) = C) (hQeq : E ⊔ C = Q) (hcyc : IsCyclic C)
    (hΩ : ∀ y ∈ C, y ^ p = 1 → y ∈ E) : IsPGroup p (Subgroup.centralizer (E : Set X)) := by
  have hp := (Fact.out : p.Prime)
  have hCn : C.Normal := by rw [← hQC]; infer_instance
  have hCQ : C ≤ Q := hQeq ▸ le_sup_right
  refine CFSG.SectionRank.Ccomm.isPGroup_of_forall_prime_orderOf ?_
  rintro ⟨d, hd⟩ ℓ hℓ hdℓ
  by_contra hne
  have hdℓ' : orderOf d = ℓ := by rw [← Subgroup.orderOf_mk d hd]; exact hdℓ
  have hdpow : d ^ ℓ = 1 := hdℓ' ▸ pow_orderOf_eq_one d
  have hm : p.Coprime ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hne)
  obtain ⟨c₀, hc₀⟩ := hcyc.exists_generator
  have hgen : ∀ y ∈ C, y ∈ Subgroup.zpowers (c₀ : X) := fun y hy => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc₀ ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hzle : Subgroup.zpowers (c₀ : X) ≤ C := Subgroup.zpowers_le.mpr c₀.2
  obtain ⟨n, hn⟩ := (hQp.to_le hCQ) c₀
  have hdC : ∀ y ∈ C, d * y * d⁻¹ = y := by
    have hcl : d * (c₀ : X) * d⁻¹ ∈ Subgroup.zpowers (c₀ : X) :=
      hgen _ (hCn.conj_mem _ c₀.2 d)
    have hΩ' : ∀ y ∈ Subgroup.zpowers (c₀ : X), y ^ p = 1 → d * y * d⁻¹ = y := by
      intro y hy hyp
      have h1 : y * d = d * y := Subgroup.mem_centralizer_iff.mp hd y (hΩ y (hzle hy) hyp)
      rw [← h1]
      group
    have hcomm := conj_eq_of_coprime_of_zpowers hm d hdpow n (c₀ : X) (congrArg Subtype.val hn)
      hcl hΩ'
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen y hy)
    rw [← hk, ← conj_zpow, hcomm]
  have hdQ : d ∈ Subgroup.centralizer (Q : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨g, hg, y, hy, rfl⟩ := exists_mul_eq_of_mem_sup_normal (hQeq ▸ hq)
    have h1 : g * d = d * g := Subgroup.mem_centralizer_iff.mp hd g hg
    have h2 : d * y = y * d := by
      have := hdC y hy
      calc d * y = d * y * d⁻¹ * d := by group
        _ = y * d := by rw [this]
    calc g * y * d = g * (y * d) := by group
      _ = g * (d * y) := by rw [h2]
      _ = (g * d) * y := by group
      _ = (d * g) * y := by rw [h1]
      _ = d * (g * y) := by group
  obtain ⟨m, hm'⟩ := hQp ⟨d, hQc hdQ⟩
  have hdm : d ^ (p ^ m) = 1 := congrArg Subtype.val hm'
  have hdvd : ℓ ∣ p ^ m := hdℓ' ▸ orderOf_dvd_of_pow_eq_one hdm
  exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hdvd))

end Burnside

end CFSG.LocalAnalysis.RankThreeTheoremC
