module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

@[expose] def zOf {Y : Type*} [Group Y] (T : Subgroup Y) : Subgroup Y :=
  T ⊓ centralizer (T : Set Y)

structure PGroupData (p : ℕ) {Y : Type*} [Group Y] (P T D : Subgroup Y) (x : Y) : Prop where
  T_le : T ≤ P
  D_le : D ≤ P
  sup_eq : T ⊔ D = P
  inf_eq : T ⊓ D = ⊥
  comm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t
  T_card : Nat.card T = p ^ 3
  T_exp : ∀ t ∈ T, t ^ p = 1
  T_nonab : ¬ IsMulCommutative T
  D_cyc : IsCyclic D
  x_mem : x ∈ D
  x_ord : orderOf x = p

structure TorusProps (p : ℕ) {Y : Type*} [Group Y] (T F : Subgroup Y) : Prop where
  F_T : ∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T
  irred : ∀ A : Subgroup Y, A ≤ T → zOf T ≤ A → (∀ f ∈ F, ∀ a ∈ A, f * a * f⁻¹ ∈ A) →
    A = zOf T ∨ A = T
  fpf : ∀ t ∈ T, (∀ f ∈ F, f * t * f⁻¹ * t⁻¹ ∈ zOf T) → t ∈ zOf T
  onto : ∀ z ∈ zOf T, ∀ k : ℕ, ¬ p ∣ k → ∃ f ∈ F, f * z * f⁻¹ = z ^ k

structure CentSeries (p : ℕ) {Y : Type*} [Group Y] (W P N : Subgroup Y) : Prop where
  P_le : P ≤ W
  N_le : N ≤ W
  N_norm : ∀ c ∈ W, ∀ n ∈ N, c * n * c⁻¹ ∈ N
  PN_norm : ∀ c ∈ W, ∀ q ∈ P ⊔ N, c * q * c⁻¹ ∈ P ⊔ N
  N_cop : ∀ n ∈ N, Nat.Coprime p (orderOf n)

structure Case2Data (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P T D F : Subgroup Y) (x : Y) : Prop where
  prime : p.Prime
  five : 5 ≤ p
  core : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  rank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3
  sylow : ∃ S : Sylow p Y, (S : Subgroup Y) = P
  pdata : PGroupData p P T D x
  torus : TorusProps p T F
  F_D : ∀ f ∈ F, ∀ d ∈ D, f * d * f⁻¹ = d
  series : ∃ N : Subgroup Y, CentSeries p (centralizer ({x} : Set Y)) P N
  wc : ∀ g : Y, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ P →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem fact (h : Case2Data p P T D F x) : Fact p.Prime := ⟨h.prime⟩

theorem zOf_card (h : Case2Data p P T D F x) : Nat.card (zOf T) = p := by
  haveI := h.fact
  exact card_inf_centralizer_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab

theorem zOf_le (h : Case2Data p P T D F x) : zOf T ≤ T := inf_le_left

theorem commutator_mem (h : Case2Data p P T D F x) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  haveI := h.fact
  have hZ : Nat.card (center T) = p :=
    card_center_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab
  have hQ : Nat.card (T ⧸ center T) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [h.pdata.T_card, hZ] at h1
    apply Nat.eq_of_mul_eq_mul_right h.prime.pos
    rw [← h1]
    ring
  have hcomm : IsMulCommutative (T ⧸ center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  intro a ha b hb
  have key : (⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ ∈ center T := by
    rw [← QuotientGroup.eq_one_iff]
    have hab := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ center T)
      (QuotientGroup.mk ⟨b, hb⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hab
  refine Subgroup.mem_inf.mpr
    ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := mem_center_iff.mp key ⟨s, hs⟩
  exact congrArg Subtype.val this

private theorem exists_mul_aux (h : Case2Data p P T D F x) :
    ∀ a ∈ P, ∃ t ∈ T, ∃ d ∈ D, a = t * d := by
  intro a ha
  have hP : P = T ⊔ D := h.pdata.sup_eq.symm
  let S : Subgroup Y :=
    { carrier := {a | ∃ t ∈ T, ∃ d ∈ D, a = t * d}
      mul_mem' := by
        rintro _ _ ⟨t, ht, d, hd, rfl⟩ ⟨t', ht', d', hd', rfl⟩
        refine ⟨t * t', T.mul_mem ht ht', d * d', D.mul_mem hd hd', ?_⟩
        have hc : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
        calc t * d * (t' * d') = t * (d * t') * d' := by group
          _ = t * (t' * d) * d' := by rw [hc]
          _ = t * t' * (d * d') := by group
      one_mem' := ⟨1, T.one_mem, 1, D.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨t, ht, d, hd, rfl⟩
        refine ⟨t⁻¹, T.inv_mem ht, d⁻¹, D.inv_mem hd, ?_⟩
        rw [mul_inv_rev]
        exact (h.pdata.comm t⁻¹ (T.inv_mem ht) d⁻¹ (D.inv_mem hd)).symm }
  have hle : T ⊔ D ≤ S :=
    sup_le (fun t ht => ⟨t, ht, 1, D.one_mem, (mul_one t).symm⟩)
      (fun d hd => ⟨1, T.one_mem, d, hd, (one_mul d).symm⟩)
  rw [hP] at ha
  exact hle ha

theorem exists_mul (h : Case2Data p P T D F x) : ∀ a ∈ P, ∃ t ∈ T, ∃ d ∈ D, a = t * d :=
  exists_mul_aux h

private theorem isPGroup_P (h : Case2Data p P T D F x) : IsPGroup p P := by
  obtain ⟨S, hS⟩ := h.sylow
  subst hS
  exact S.isPGroup'

theorem exists_pow_eq_one (h : Case2Data p P T D F x) : ∀ a ∈ P, ∃ k : ℕ, a ^ (p ^ k) = 1 := by
  intro a ha
  obtain ⟨k, hk⟩ := isPGroup_P h ⟨a, ha⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem x_ne_one (h : Case2Data p P T D F x) : x ≠ 1 := by
  intro hx
  have h1 := h.pdata.x_ord
  rw [hx, orderOf_one] at h1
  have h2 := h.prime.one_lt
  omega

private theorem mem_zpowers_aux (h : Case2Data p P T D F x) :
    ∀ d ∈ D, d ^ p = 1 → d ∈ zpowers x := by
  classical
  haveI := h.fact
  haveI : IsCyclic D := h.pdata.D_cyc
  haveI : Fintype D := Fintype.ofFinite D
  intro d hd hdp
  obtain ⟨x', hx'⟩ : ∃ x' : D, (x' : Y) = x := ⟨⟨x, h.pdata.x_mem⟩, rfl⟩
  have hx'ord : orderOf x' = p := by
    rw [← h.pdata.x_ord, ← hx', Subgroup.orderOf_coe]
  have hx'p : x' ^ p = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'ord] at this
  have hsub : (zpowers x' : Set D) ⊆ {a : D | a ^ p = 1} := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    show (x' ^ k) ^ p = 1
    calc (x' ^ k) ^ p = (x' ^ k) ^ (p : ℤ) := (zpow_natCast _ _).symm
      _ = x' ^ (k * p) := (zpow_mul _ _ _).symm
      _ = x' ^ ((p : ℤ) * k) := by rw [mul_comm]
      _ = (x' ^ (p : ℤ)) ^ k := zpow_mul _ _ _
      _ = 1 := by rw [zpow_natCast, hx'p, one_zpow]
  have hfin : ({a : D | a ^ p = 1} : Set D).Finite := Set.toFinite _
  have hcard1 : Nat.card ({a : D | a ^ p = 1} : Set D) ≤ p := by
    have h1 : ({a : D | a ^ p = 1} : Set D) =
        ↑(Finset.univ.filter (fun a : D => a ^ p = 1)) := by
      ext a
      simp
    rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact IsCyclic.card_pow_eq_one_le h.prime.pos
  have hcard2 : p ≤ Nat.card (zpowers x' : Set D) := by
    have : Nat.card (zpowers x') = p := by rw [Nat.card_zpowers, hx'ord]
    exact this.ge
  have heq : (zpowers x' : Set D) = {a : D | a ^ p = 1} :=
    Set.Finite.eq_of_subset_of_card_le hfin hsub (hcard1.trans hcard2)
  have hdmem : (⟨d, hd⟩ : D) ∈ zpowers x' := by
    have h1 : (⟨d, hd⟩ : D) ∈ ({a : D | a ^ p = 1} : Set D) := by
      show (⟨d, hd⟩ : D) ^ p = 1
      exact Subtype.ext (by simpa using hdp)
    rw [← heq] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdmem
  have h2 := congrArg Subtype.val hk
  simp only [Subgroup.coe_zpow, hx'] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem x_mem_of_ne_bot (h : Case2Data p P T D F x) :
    ∀ C : Subgroup Y, C ≤ D → C ≠ ⊥ → x ∈ C := by
  haveI := h.fact
  intro C hCD hC
  have hCP : C ≤ P := hCD.trans h.pdata.D_le
  have hCp : IsPGroup p C :=
    (isPGroup_P h).of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC
  obtain ⟨n, hn, hcard⟩ := hCp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card C := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcY : orderOf (c : Y) = p := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcp : (c : Y) ^ p = 1 := by
    have := pow_orderOf_eq_one (c : Y)
    rwa [hcY] at this
  have hcx : (c : Y) ∈ zpowers x := mem_zpowers_aux h (c : Y) (hCD c.2) hcp
  have hle : zpowers (c : Y) ≤ zpowers x := Subgroup.zpowers_le.mpr hcx
  have hcard' : Nat.card (zpowers x) ≤ Nat.card (zpowers (c : Y)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcY, h.pdata.x_ord]
  have heq : zpowers (c : Y) = zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard'
  have hxc : x ∈ zpowers (c : Y) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr c.2) hxc

theorem mem_zpowers_of_pow_eq_one (h : Case2Data p P T D F x) :
    ∀ d ∈ D, d ^ p = 1 → d ∈ zpowers x :=
  mem_zpowers_aux h

theorem T_inf_zpowers (h : Case2Data p P T D F x) : T ⊓ zpowers x = ⊥ := by
  have hz : zpowers x ≤ D := Subgroup.zpowers_le.mpr h.pdata.x_mem
  rw [eq_bot_iff, ← h.pdata.inf_eq]
  exact inf_le_inf_left T hz

theorem F_mem_normalizer_P (h : Case2Data p P T D F x) :
    ∀ f ∈ F, ∀ a ∈ P, f * a * f⁻¹ ∈ P := by
  intro f hf a ha
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_aux h a ha
  have h1 : f * (t * d) * f⁻¹ = (f * t * f⁻¹) * (f * d * f⁻¹) := by group
  rw [h1, h.F_D f hf d hd]
  exact P.mul_mem (h.pdata.T_le (h.torus.F_T f hf t ht)) (h.pdata.D_le hd)

theorem F_zOf (h : Case2Data p P T D F x) : ∀ f ∈ F, ∀ z ∈ zOf T, f * z * f⁻¹ ∈ zOf T := by
  intro f hf z hz
  obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨h.torus.F_T f hf z hzT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : f⁻¹ * s * f ∈ T := by
    have := h.torus.F_T f⁻¹ (F.inv_mem hf) s hs
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hzC (f⁻¹ * s * f) hs'
  calc s * (f * z * f⁻¹) = f * ((f⁻¹ * s * f) * z) * f⁻¹ := by group
    _ = f * (z * (f⁻¹ * s * f)) * f⁻¹ := by rw [hc]
    _ = (f * z * f⁻¹) * s := by group

theorem F_fixed (h : Case2Data p P T D F x) :
    ∀ z ∈ zOf T, (∀ f ∈ F, f * z * f⁻¹ = z) → z = 1 := by
  intro z hz hfix
  have hnd : ¬ p ∣ 2 := by
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := h.five
    omega
  obtain ⟨f, hf, hfz⟩ := h.torus.onto z hz 2 hnd
  rw [hfix f hf] at hfz
  have h3 : z * z = z * 1 := by
    rw [mul_one, ← pow_two]
    exact hfz.symm
  exact mul_left_cancel h3

theorem central_form (h : Case2Data p P T D F x) {u : Y} (hu : u ∈ P)
    (hc : ∀ a ∈ P, u * a = a * u) (hp : u ^ p = 1) :
    ∃ t ∈ zOf T, ∃ j : ℕ, u = t * x ^ j := by
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_aux h u hu
  have htz : t ∈ zOf T := by
    refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hc s (h.pdata.T_le hs)
    have h2 : d * s = s * d := (h.pdata.comm s hs d hd).symm
    have h3 : s * t * d = t * s * d := by
      calc s * t * d = s * (t * d) := by group
        _ = t * d * s := h1.symm
        _ = t * (d * s) := by group
        _ = t * (s * d) := by rw [h2]
        _ = t * s * d := by group
    exact mul_right_cancel h3
  have hdp : d ^ p = 1 := by
    have hcomm : Commute t d := h.pdata.comm t ht d hd
    rw [hcomm.mul_pow p, h.pdata.T_exp t ht, one_mul] at hp
    exact hp
  have hdx : d ∈ zpowers x := mem_zpowers_aux h d hd hdp
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hdx)
  exact ⟨t, htz, j, by rw [hj]⟩

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
