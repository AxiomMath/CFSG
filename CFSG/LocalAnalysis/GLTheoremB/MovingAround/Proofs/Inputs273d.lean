module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz6b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner
public import CFSG.HardMathSupport.Dickson.Bal207.ExcSz32
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf innerAut IsCompLocallyBalanced)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)

theorem exists_index_of_typeChevQ {p : ℕ} {S : Type} [Group S] (h : Inputs273.TypeChevQ p S) :
    ∃ d : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      p ≠ d.1.characteristic := by
  obtain ⟨⟨q, -, -, hc⟩, hnp, hna⟩ := h
  have key : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ d : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
        p ≠ d.1.characteristic := fun d ⟨e⟩ =>
    ⟨d, ⟨e⟩, fun hpd => hnp (Or.inl ⟨.lie d, hpd.symm, ⟨e⟩⟩)⟩
  rcases hc with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
    · exact key d ⟨e⟩
    · simp [CFSG.Yardstones.Md0ec50421ce4.onLie] at hi
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    · exact absurd ⟨n, ⟨e⟩⟩ hna
    · exact key d ⟨e⟩
    · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

section Powers

variable {G : Type*} [Group G]

theorem conj_pow_eq_zpow {x z : G} {m : ℤ} (h : x * z * x⁻¹ = z ^ m) (n : ℕ) :
    x ^ n * z * (x ^ n)⁻¹ = z ^ (m ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * z * (x ^ (n + 1))⁻¹ = x * (x ^ n * z * (x ^ n)⁻¹) * x⁻¹ := by group
      _ = x * z ^ (m ^ n) * x⁻¹ := by rw [ih]
      _ = (x * z * x⁻¹) ^ (m ^ n) := conj_zpow.symm
      _ = z ^ (m ^ (n + 1)) := by rw [h, ← zpow_mul, pow_succ']

theorem mul_pow_eq_zpow_mul {x z : G} {m : ℤ} (h : x * z * x⁻¹ = z ^ m) (n : ℕ) :
    (z * x) ^ n = z ^ (∑ i ∈ Finset.range n, m ^ i) * x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (z * x) ^ (n + 1)
        = z ^ (∑ i ∈ Finset.range n, m ^ i) * (x ^ n * z * (x ^ n)⁻¹) * x ^ (n + 1) := by
          rw [pow_succ, ih]
          simp only [mul_assoc, pow_succ, inv_mul_cancel_left]
      _ = z ^ (∑ i ∈ Finset.range (n + 1), m ^ i) * x ^ (n + 1) := by
          rw [conj_pow_eq_zpow h n, Finset.sum_range_succ, zpow_add]

end Powers

section NumberTheory

theorem one_add_mul_pow_eq (a t : ℤ) (n : ℕ) :
    ∃ w : ℤ, (1 + a * t) ^ n = 1 + n * (a * t) + a ^ 2 * w := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨n * t ^ 2 + w + w * a * t, by rw [pow_succ, hw]; push_cast; ring⟩

theorem sum_one_add_mul_pow_eq (a t : ℤ) (n : ℕ) :
    ∃ W : ℤ, ∑ i ∈ Finset.range n, (1 + a * t) ^ i =
      n + a * t * (∑ i ∈ Finset.range n, (i : ℤ)) + a ^ 2 * W := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨W, hW⟩ := ih
    obtain ⟨w, hw⟩ := one_add_mul_pow_eq a t n
    exact ⟨W + w, by rw [Finset.sum_range_succ, Finset.sum_range_succ, hW, hw]; push_cast; ring⟩

theorem not_sq_dvd_geom_sum {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : ℤ} (hu : (p : ℤ) ∣ u - 1) :
    ¬ ((p : ℤ) ^ 2 ∣ ∑ i ∈ Finset.range p, u ^ i) := by
  obtain ⟨t, ht⟩ := hu
  have hu' : u = 1 + p * t := by linarith
  obtain ⟨W, hW⟩ := sum_one_add_mul_pow_eq (p : ℤ) t p
  obtain ⟨c, hc⟩ : ∃ c : ℕ, p = 2 * c + 1 := hp.odd_of_ne_two hp2
  have hsumN : (∑ i ∈ Finset.range p, i) = p * c := by
    have h := Finset.sum_range_id_mul_two p
    have hp1 : p - 1 = 2 * c := by omega
    rw [hp1] at h
    have h2 : (∑ i ∈ Finset.range p, i) * 2 = (p * c) * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hsum : ∑ i ∈ Finset.range p, (i : ℤ) = p * c := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hsumN
    simpa using h
  intro hdvd
  rw [hu', hW, hsum] at hdvd
  have h2 : ((p : ℤ) ^ 2) ∣ (p : ℤ) := by
    have e : (p : ℤ) + p * t * (p * c) + p ^ 2 * W = p + p ^ 2 * (t * c + W) := by ring
    rw [e] at hdvd
    exact (dvd_add_left (dvd_mul_right _ _)).1 hdvd
  have h3 : p ^ 2 ∣ p := by exact_mod_cast h2
  have h4 := Nat.le_of_dvd hp.pos h3
  have h5 := hp.two_le
  nlinarith

theorem pow_prime_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x z : G} {m : ℤ}
    (hm : x * z * x⁻¹ = z ^ m) (hx : x ^ p = 1) {b : ℕ} (hzb : orderOf z = p ^ b)
    (hzx : (z * x) ^ p = 1) : z ^ p = 1 := by
  have hS : z ^ (∑ i ∈ Finset.range p, m ^ i) = 1 := by
    have h := mul_pow_eq_zpow_mul hm p
    rw [hx, mul_one, hzx] at h
    exact h.symm
  have hfix : z ^ (m ^ p - 1) = 1 := by
    have h := conj_pow_eq_zpow hm p
    rw [hx, one_mul, inv_one, mul_one] at h
    rw [zpow_sub, zpow_one, ← h, mul_inv_cancel]
  rcases Nat.lt_or_ge b 2 with hb | hb
  · rw [← orderOf_dvd_iff_pow_eq_one, hzb]
    exact (pow_dvd_pow p (by omega : b ≤ 1)).trans (by rw [pow_one])
  · exfalso
    have h1 : (p : ℤ) ^ 2 ∣ (orderOf z : ℤ) := by
      rw [hzb]
      push_cast
      exact pow_dvd_pow _ hb
    have h2 : (orderOf z : ℤ) ∣ ∑ i ∈ Finset.range p, m ^ i := orderOf_dvd_iff_zpow_eq_one.2 hS
    have h3 : (orderOf z : ℤ) ∣ m ^ p - 1 := orderOf_dvd_iff_zpow_eq_one.2 hfix
    have h4 : (p : ℤ) ∣ m - 1 := by
      have hpm : (p : ℤ) ∣ m ^ p - 1 := ((dvd_pow_self (p : ℤ) two_ne_zero).trans h1).trans h3
      have hF := Int.prime_dvd_pow_self_sub hp m
      have e : m - 1 = (m ^ p - 1) - (m ^ p - m) := by ring
      rw [e]
      exact dvd_sub hpm hF
    exact not_sq_dvd_geom_sum hp hp2 h4 (h1.trans h2)

theorem conj_eq_self_of_pow_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e z : G} {m : ℤ}
    (hm : e * z * e⁻¹ = z ^ m) (he : e ^ p = 1) (hz : z ^ p = 1) : e * z * e⁻¹ = z := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, mul_inv_cancel]
  have hzo : orderOf z = p := orderOf_eq_prime hz hz1
  have hfix := conj_pow_eq_zpow hm p
  rw [he, one_mul, inv_one, mul_one] at hfix
  have h0 : z ^ (m ^ p - 1) = 1 := by rw [zpow_sub, zpow_one, ← hfix, mul_inv_cancel]
  have h1 : (p : ℤ) ∣ m ^ p - 1 := by
    have h := orderOf_dvd_iff_zpow_eq_one.2 h0
    rwa [hzo] at h
  have h2 : (p : ℤ) ∣ m - 1 := by
    have hF := Int.prime_dvd_pow_self_sub hp m
    have e : m - 1 = (m ^ p - 1) - (m ^ p - m) := by ring
    rw [e]
    exact dvd_sub h1 hF
  have h3 : z ^ (m - 1) = 1 := by
    rw [← hzo] at h2
    exact orderOf_dvd_iff_zpow_eq_one.1 h2
  rw [hm]
  calc z ^ m = z ^ (m - 1) * z := by rw [← zpow_add_one, sub_add_cancel]
    _ = z := by rw [h3, one_mul]

end NumberTheory

section Center

theorem isCyclic_center_of_pRank_le_one {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZp : IsPGroup p ↥(Subgroup.center Y)) (hr : CFSG.Open.pRank p (Subgroup.center Y) ≤ 1) :
    IsCyclic ↥(Subgroup.center Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p ↥(Subgroup.center Y)) := ⟨hZp⟩
  by_contra hnc
  obtain ⟨F, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := p) hp2 hnc
  have hF : IsElemAbelian p F := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p F).mp hel
  have hF' := CFSG.SectionRank.isElemAbelian_map hF (Subgroup.center Y).subtype
  have hcard' : Nat.card (F.map (Subgroup.center Y).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard]
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le F) hF' hcard'
  omega

theorem isCyclic_center (hGA : CFSG.Open.GriessAllModelsStatement) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore p Y = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) : IsCyclic ↥(Subgroup.center Y) :=
  isCyclic_center_of_pRank_le_one hp hp2 (Inputs273.isPGroup_center_of_core hp hO)
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.center64_of_griess hGA p hp hp2 Y hq hO d ⟨e⟩ hpd)

theorem exists_conj_eq_zpow {X : Type*} [Group X] {K : Subgroup X} (hcyc : IsCyclic ↥(Subgroup.center ↥K))
    {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X)) :
    ∃ m : ℤ, ∀ c : ↥K, c ∈ Subgroup.center ↥K → x * (c : X) * x⁻¹ = (c : X) ^ m := by
  set φ : MulAut ↥K := K.normalizerMonoidHom ⟨x, hx⟩ with hφ
  have hφc : ∀ c : ↥K, c ∈ Subgroup.center ↥K → φ c ∈ Subgroup.center ↥K := by
    intro c hc
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    obtain ⟨h, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hc h]
  let σ : ↥(Subgroup.center ↥K) →* ↥(Subgroup.center ↥K) :=
    { toFun := fun c => ⟨φ (c : ↥K), hφc (c : ↥K) c.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : ↥K) (b : ↥K)) }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (h := hcyc) σ
  refine ⟨m, fun c hc => ?_⟩
  have h1 := congrArg (fun w : ↥(Subgroup.center ↥K) => ((w : ↥K) : X)) (hm ⟨c, hc⟩)
  simp only [σ, MonoidHom.coe_mk, OneHom.coe_mk, SubgroupClass.coe_zpow] at h1
  rw [← h1, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]

end Center

section Lift

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem mem_normalizer_of_conj (hp : p.Prime) (hp2 : p ≠ 2) {E K : Subgroup X} (hE : IsSCp p ⊤ E)
    (hN : E ≤ Subgroup.normalizer (K : Set X)) (hcyc : IsCyclic ↥(Subgroup.center ↥K))
    (hZp : IsPGroup p ↥(Subgroup.center ↥K)) {x : X} (hx : x ∈ E) (k z : ↥K) (hz : z ∈ Subgroup.center ↥K)
    (hxk : x * (k : X) * x⁻¹ = (k : X) * (z : X)) :
    (k : X) ∈ Subgroup.normalizer
      ((Subgroup.zpowers x ⊔ (E ⊓ Subgroup.centralizer (K : Set X)) : Subgroup X) : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hE.2.1.2 x hx
  have h1 : (k : X)⁻¹ * x * (k : X) = (z : X) * x := by
    calc (k : X)⁻¹ * x * (k : X) = (k : X)⁻¹ * (x * (k : X) * x⁻¹) * x := by group
      _ = (z : X) * x := by rw [hxk]; group
  have h2 : ((z : X) * x) ^ p = 1 := by
    rw [← h1]
    have h := conj_pow (i := p) (a := (k : X)⁻¹) (b := x)
    rw [inv_inv] at h
    rw [h, hxp, mul_one, inv_mul_cancel]
  obtain ⟨m, hm⟩ := exists_conj_eq_zpow hcyc (hN hx)
  obtain ⟨b, hb⟩ : ∃ b : ℕ, orderOf (z : X) = p ^ b := by
    obtain ⟨n, hn⟩ := hZp ⟨z, hz⟩
    have h3 : (z : X) ^ p ^ n = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center ↥K) => ((w : ↥K) : X)) hn
      simpa using this
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h3)
    exact ⟨b, hb⟩
  have hzp : (z : X) ^ p = 1 := pow_prime_eq_one hp hp2 (hm z hz) hxp hb h2
  have hEz : ∀ e ∈ E, e * (z : X) = (z : X) * e := by
    intro e he
    obtain ⟨me, hme⟩ := exists_conj_eq_zpow hcyc (hN he)
    have h3 := conj_eq_self_of_pow_prime hp (hme z hz) (hE.2.1.2 e he) hzp
    calc e * (z : X) = e * (z : X) * e⁻¹ * e := by group
      _ = (z : X) * e := by rw [h3]
  have hzE : (z : X) ∈ E := by
    have hel := Inputs27.isElemAbelian_sup_of_commute hE.2.1 (Inputs27.isElemAbelian_zpowers' hzp)
      (fun e he w hw => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        exact (Commute.zpow_right (hEz e he) j).eq)
    have heq := hE.2.2 _ le_top hel le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hzC : (z : X) ∈ E ⊓ Subgroup.centralizer (K : Set X) := by
    refine ⟨hzE, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
    exact congrArg Subtype.val this
  set D : Subgroup X := Subgroup.zpowers x ⊔ (E ⊓ Subgroup.centralizer (K : Set X)) with hD
  have hmap : D.map (MulAut.conj (k : X)⁻¹).toMonoidHom ≤ D := by
    rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      have hx' : (MulAut.conj (k : X)⁻¹).toMonoidHom x = (z : X) * x := by
        rw [← h1]
        simp [MulAut.conj_apply]
      rw [hx']
      exact D.mul_mem (Subgroup.mem_sup_right hzC) (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    · rintro _ ⟨c, hc, rfl⟩
      have hck : (k : X) * c = c * (k : X) := Subgroup.mem_centralizer_iff.1 hc.2 (k : X) k.2
      have hc' : (MulAut.conj (k : X)⁻¹).toMonoidHom c = c := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc (k : X)⁻¹ * c * (k : X) = (k : X)⁻¹ * ((k : X) * c) := by rw [hck]; group
          _ = c := by group
      rw [hc']
      exact Subgroup.mem_sup_right hc
  have heq : GLBConj (k : X) D = D :=
    Subgroup.eq_of_le_of_card_ge hmap
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (k : X)⁻¹).injective).symm)
  exact mem_normalizer_iff_gLBConj_eq.2 heq

theorem two_le_pRank_zpowers_sup (hp : p.Prime) {E C : Subgroup X} (hE : IsElemAbelian p E) (hCE : C ≤ E)
    (hC : C ≠ ⊥) {x : X} (hx : x ∈ E) (hxC : x ∉ C) :
    2 ≤ CFSG.Open.pRank p (Subgroup.zpowers x ⊔ C) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := fun h => hxC (h ▸ C.one_mem)
  have hxo : orderOf x = p := orderOf_eq_prime (hE.2 x hx) hx1
  have hxc : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxo]
  have hCel : IsElemAbelian p C := CFSG.Open.IsElemAbelian.mono hE hCE
  have hinf : Subgroup.zpowers x ⊓ C = ⊥ := by
    have hd : Nat.card ↥(Subgroup.zpowers x ⊓ C) ∣ p := hxc ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers x ⊓ C = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hxc])
      exact hxC ((heq ▸ inf_le_right : Subgroup.zpowers x ≤ C) (Subgroup.mem_zpowers x))
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    Inputs27.elem_mul_comm hE ((Subgroup.zpowers_le.2 hx) ha) (hCE hc)
  have hcard := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcomm hinf
  have hCp : p ≤ Nat.card C := by
    rw [Inputs27.card_eq_pow_pRank hp hCel]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ CFSG.Open.pRank p C :=
        Nat.pow_le_pow_right hp.pos (Inputs27.one_le_pRank_of_ne_bot hp hCel hC)
  have hel : IsElemAbelian p (Subgroup.zpowers x ⊔ C) :=
    Inputs27.isElemAbelian_sup_of_commute (Inputs27.isElemAbelian_zpowers' (hE.2 x hx)) hCel hcomm
  refine InputsSeitz3.two_le_pRank_of_card hp hel ?_
  rw [hcard, hxc, pow_two]
  exact Nat.mul_le_mul_left p hCp

theorem le_glbCore_of_plane (h2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) (hp : p.Prime) (hp2 : p ≠ 2)
    {E K : Subgroup X} (hE : IsSCp p ⊤ E) (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hq : CFSG.Open.IsQuasisimple ↥K) (hcyc : IsCyclic ↥(Subgroup.center ↥K))
    (hZp : IsPGroup p ↥(Subgroup.center ↥K)) (hC : E ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥)
    {d : TauCeti.ValidLieTypeIndex} (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hnd : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1)
    {E₂ : Subgroup X} (hE₂E : E₂ ≤ E) (hE₂C : E₂ ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hE₂c : Nat.card E₂ = p ^ 2) : K ≤ GLBCore p 2 E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : commutator ↥K = ⊤ := hq.1
  have hE₂N : E₂ ≤ Subgroup.normalizer (K : Set X) := hE₂E.trans hN
  have hE₂el : IsElemAbelian p E₂ := CFSG.Open.IsElemAbelian.mono hE.2.1 hE₂E
  have hαc : Nat.card (InputsSeitz3.autIm E₂ K) = p ^ 2 :=
    (InputsSeitz3.card_autIm hE₂N hE₂C).trans hE₂c
  have hαel := InputsSeitz3.isElemAbelian_autIm hE₂el K
  have hψ := quotientCenterAut'_injective hperf
  have hPc : Nat.card ((InputsSeitz3.autIm E₂ K).map (quotientCenterAut' ↥K)) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hψ, hαc]
  have hPel := CFSG.SectionRank.isElemAbelian_map hαel (quotientCenterAut' ↥K)
  have hgen := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.planeGen_of_kfact h2 hp hp2 d e hpd hnd hPel hPc
  set H : Subgroup ↥K := (GLBCore p 2 E).subgroupOf K with hH
  have hsub : {s : ↥K ⧸ Subgroup.center ↥K | ∃ f ∈ (InputsSeitz3.autIm E₂ K).map (quotientCenterAut' ↥K),
      f ≠ 1 ∧ f s = s} ⊆ (H.map (QuotientGroup.mk' (Subgroup.center ↥K)) : Set (↥K ⧸ Subgroup.center ↥K)) := by
    rintro s ⟨f, hfP, hf1, hfs⟩
    obtain ⟨φ, hφα, rfl⟩ := Subgroup.mem_map.1 hfP
    obtain ⟨n, hnE, rfl⟩ := Subgroup.mem_map.1 hφα
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
    have hnE' : (n : X) ∈ E₂ := Subgroup.mem_subgroupOf.1 hnE
    have hfix : (QuotientGroup.mk (K.normalizerMonoidHom n k) : ↥K ⧸ Subgroup.center ↥K) =
        QuotientGroup.mk k := hfs
    have hz : k⁻¹ * K.normalizerMonoidHom n k ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hfix.symm
    have hconj : (n : X) * (k : X) * (n : X)⁻¹ =
        (k : X) * ((k⁻¹ * K.normalizerMonoidHom n k : ↥K) : X) := by
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    have hkN := mem_normalizer_of_conj hp hp2 hE hN hcyc hZp (hE₂E hnE') k _ hz hconj
    have hnC : (n : X) ∉ E ⊓ Subgroup.centralizer (K : Set X) := by
      intro hnC
      apply hf1
      have hn1 : (n : X) = 1 := by
        have h0 : (n : X) ∈ E₂ ⊓ Subgroup.centralizer (K : Set X) := ⟨hnE', hnC.2⟩
        rwa [hE₂C, Subgroup.mem_bot] at h0
      have hn1' : n = 1 := Subtype.ext hn1
      rw [hn1', map_one, map_one]
    have hD2 := two_le_pRank_zpowers_sup hp hE.2.1 inf_le_left hC (hE₂E hnE') hnC
    have hle := Inputs27.normalizer_le_glbCore'
      (sup_le (Subgroup.zpowers_le.2 (hE₂E hnE')) inf_le_left) hD2
    exact ⟨k, Subgroup.mem_subgroupOf.2 (hle hkN), rfl⟩
  have hmap : H.map (QuotientGroup.mk' (Subgroup.center ↥K)) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hsub
  have hsup : H ⊔ Subgroup.center ↥K = ⊤ := by
    have h := QuotientGroup.comap_map_mk' (Subgroup.center ↥K) H
    rw [hmap, Subgroup.comap_top] at h
    rw [sup_comm, ← h]
  have hHtop := CFSG.HardMathSupport.Dickson.I271.eq_top_of_sup_center_eq_top hperf hsup
  intro x hx
  have hxH : (⟨x, hx⟩ : ↥K) ∈ H := by
    rw [hHtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hxH

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← hZ, Subgroup.mem_center_iff]
  intro h
  have h1 := congrArg (fun φ : MulAut K => φ h) (MonoidHom.mem_ker.1 hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc h * g = g * h * g⁻¹ * g := by rw [h1]
    _ = g * h := by group

end Lift

section SpTwo

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_spTwo {E K : Subgroup X} (hE : IsSCp 3 ⊤ E)
    (hN : E ≤ Subgroup.normalizer (K : Set X)) (hC : E ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥)
    (h27 : 3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card E)
    (hZ : Subgroup.center ↥K = ⊥) {n : ℕ} (hn : 3 ≤ n) {q : TauCeti.PrimePower} (hqp : q.p = 2)
    (hqe : q.exponent = 1) {hv : (TauCeti.LieTypeIndex.B n q).Valid}
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group) : K ≤ GLBCore 3 2 E := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨e₂⟩ := nonempty_typeBGroupEquiv_spTwo hn q hv hqp hqe
  set ψ : ↥K ≃* ↥(CFSG.Open.StatedSp n (ZMod 2)) := eK.trans e₂ with hψ
  have hinn : ∀ α : MulAut ↥K, α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    intro α
    obtain ⟨g, hg⟩ := all_inner_spTwo hn (MulAut.congr ψ α)
    refine ⟨ψ.symm g, MulEquiv.ext fun x => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥(CFSG.Open.StatedSp n (ZMod 2)) => φ (ψ x)) hg
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [MulAut.conj_apply]
    apply ψ.injective
    rw [h1]
    simp
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := conj_injective_of_center_eq_bot hZ
  have hcyc : IsCyclic ↥(Subgroup.center ↥K) := by
    rw [hZ]
    infer_instance
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥K) := by
    rw [hZ]
    exact IsPGroup.of_bot
  obtain ⟨E₃, hE₃N, hE₃C, hE₃c⟩ := InputsSeitz3.exists_faithful hp hE.2.1 (k := 3)
    (by rw [show GL83.CompFam.stab E K = E from inf_eq_left.2 hN]; exact h27)
  have hE₃E : E₃ ≤ E := hE₃N.trans inf_le_left
  have hE₃NK : E₃ ≤ Subgroup.normalizer (K : Set X) := hE₃E.trans hN
  have hAel := InputsSeitz3.isElemAbelian_autIm (CFSG.Open.IsElemAbelian.mono hE.2.1 hE₃E) K
  have hmap : ((InputsSeitz3.autIm E₃ K).comap (MulAut.conj : ↥K →* MulAut ↥K)).map MulAut.conj =
      InputsSeitz3.autIm E₃ K :=
    Subgroup.map_comap_eq_self fun α _ => hinn α
  have hE'c : Nat.card ((InputsSeitz3.autIm E₃ K).comap (MulAut.conj : ↥K →* MulAut ↥K)) = 3 ^ 3 := by
    rw [← (InputsSeitz3.card_autIm hE₃NK hE₃C).trans hE₃c]
    conv_rhs => rw [← hmap]
    rw [Subgroup.card_map_of_injective hconj]
  have hE'el := isElemAbelian_comap_of_injective hconj hAel
  have hDel := CFSG.SectionRank.isElemAbelian_map hE'el ψ.toMonoidHom
  have hDc : Nat.card (((InputsSeitz3.autIm E₃ K).comap (MulAut.conj : ↥K →* MulAut ↥K)).map
      ψ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE'c]
    norm_num
  obtain ⟨Q, hQD, -, hgen⟩ := exists_plane_closure_centralizers_eq_top (by omega) hDel hDc
  set Γ : Subgroup ↥K := (GLBCore 3 2 E).subgroupOf K with hΓ
  have hcl : (⊤ : Subgroup ↥(CFSG.Open.StatedSp n (ZMod 2))) ≤ Γ.map ψ.toMonoidHom := by
    rw [← hgen, Subgroup.closure_le]
    rintro g ⟨y, hyQ, hy1, hgy⟩
    obtain ⟨y₀, hy₀E', rfl⟩ := hQD hyQ
    obtain ⟨m, hmE, hm⟩ := hy₀E'
    have hmE' : (m : X) ∈ E₃ := Subgroup.mem_subgroupOf.1 hmE
    refine ⟨ψ.symm g, ?_, by simp⟩
    have hgy₀ : ψ.symm g * y₀ = y₀ * ψ.symm g := by
      apply ψ.injective
      simpa using hgy
    have hcomm : (m : X) * ((ψ.symm g : ↥K) : X) * (m : X)⁻¹ = ((ψ.symm g : ↥K) : X) * ((1 : ↥K) : X) := by
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe, hm, MulAut.conj_apply, OneMemClass.coe_one,
        mul_one]
      congr 1
      calc y₀ * ψ.symm g * y₀⁻¹ = ψ.symm g * y₀ * y₀⁻¹ := by rw [hgy₀]
        _ = ψ.symm g := by group
    have hkN := mem_normalizer_of_conj hp (by norm_num) hE hN hcyc hZp (hE₃E hmE') (ψ.symm g) 1
      (Subgroup.one_mem _) hcomm
    have hmC : (m : X) ∉ E ⊓ Subgroup.centralizer (K : Set X) := by
      intro hmC
      apply hy1
      have hm1 : (m : X) = 1 := by
        have h0 : (m : X) ∈ E₃ ⊓ Subgroup.centralizer (K : Set X) := ⟨hmE', hmC.2⟩
        rwa [hE₃C, Subgroup.mem_bot] at h0
      have hm1' : m = 1 := Subtype.ext hm1
      rw [hm1', map_one] at hm
      have hy01 : y₀ = 1 := hconj (hm.symm.trans (map_one _).symm)
      rw [hy01, map_one]
    have hD2 := two_le_pRank_zpowers_sup hp hE.2.1 inf_le_left hC (hE₃E hmE') hmC
    exact Subgroup.mem_subgroupOf.2
      (Inputs27.normalizer_le_glbCore' (sup_le (Subgroup.zpowers_le.2 (hE₃E hmE')) inf_le_left) hD2 hkN)
  have hΓtop : Γ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hcl (Subgroup.mem_top (ψ x))
    rw [← ψ.injective hyx]
    exact hy
  intro x hx
  have hxΓ : (⟨x, hx⟩ : ↥K) ∈ Γ := by
    rw [hΓtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.1 hxΓ

end SpTwo

section TitsFive


theorem false_of_tits_five (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 5 K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hA2 : CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut K)) ≤ 2 →
      5 ≤ 5 ∧ (5 ∣ (innerAut K).index ∨ ∃ P : Sylow 5 K, ¬ IsMulCommutative ↥(P : Subgroup K))) :
    False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hperf : commutator K = ⊤ := hq.1
  obtain ⟨-, hOS⟩ := hA2 (InputsSeitz3.pRank_five_mulAut_le_two_of_tits hperf d hd e)
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  have hZ : Subgroup.center K = ⊥ := by
    by_contra hZ
    have hdvd := InputsSeitz6.dvd_card_of_isPGroup (Inputs273.isPGroup_center_of_core Nat.prime_five hO) hZ
    exact CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM Nat.prime_five
      (by norm_num) hq _ e (by simp) hdvd
  set eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := (InputsSeitz3.equivCenterQuot hZ).trans e with heK
  obtain ⟨hcard, hout⟩ := CFSG.LieType.SeitzGeneration.card_cat_tits_outer hv
  have hKc : Nat.card K = 17971200 := (Nat.card_congr eK.toEquiv).trans hcard
  rcases hOS with hdvd | ⟨P, hP⟩
  · have h1 : (innerAut K).map (MulAut.congr eK).toMonoidHom =
        innerAut (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr eK
    have h2 := Subgroup.index_map_of_bijective (f := (MulAut.congr eK).toMonoidHom)
      (MulAut.congr eK).bijective (innerAut K)
    rw [h1] at h2
    have hidx : (innerAut K).index = 2 := by
      rw [← h2]
      exact hout
    rw [hidx] at hdvd
    norm_num at hdvd
  · apply hP
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have hdk : 5 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup K)
      have h3 : 5 ^ 3 ∣ 17971200 := hKc ▸ (Nat.pow_dvd_pow 5 hk3).trans hdk
      norm_num at h3
    exact Inputs273.isMulCommutative_of_card_le_sq Nat.prime_five hk hk2

end TitsFive

section Suzuki


variable {X : Type} [Group X] [Finite X]

theorem isCompLocallyBalanced_sz32 {K : Subgroup X} (A : Subgroup X) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hOK : GLAPPrimeCore 5 ↥K = ⊥) {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) :
    IsCompLocallyBalanced 5 1 A K :=
  (CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_mulEquiv (Inputs273.barOfEquivOfCore hOK)
    (Inputs273.isLocallyBalancedAbs_of_centerQuot hq.1
      (CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_mulEquiv e
        (CFSG.HardMathSupport.Dickson.Bal207.isLocallyBalancedAbs_five_one_sz32 hv)))).isLocallyBalanced _

theorem sz32_down (hO : GLAPPrimeCore 5 X = ⊥) {K : Subgroup X} (hK : GLAPComponent 5 ⊤ K)
    {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) {A : Subgroup X}
    (hA : IsElemAbelian 5 A) {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) {J : Subgroup X}
    (hJ : GLAPComponent 5 (GLAPLayer 5 ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J) :
    IsLocallyOTwoBalancedWrtP 5 1 (barOf 5 J) := by
  have hp : Nat.Prime 5 := Nat.prime_five
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hbal : CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs 5 1 (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_mulEquiv e
      (CFSG.HardMathSupport.Dickson.Bal207.isLocallyBalancedAbs_five_one_sz32 hv)
  have hO2K := Inputs273.isLocallyOTwoBalancedWrtP_of_abs hp (by norm_num) hbal
  have hqJ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  refine Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hqJ.1 ?_
  by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
  · obtain ⟨g, -, haL, hJL⟩ := Inputs273.exists_conj_of_mem_normalizer hp hO hK hA ha haN hJ
    have hLc := Inputs273.glaPComponent_conj hK g
    obtain ⟨-, hOL⟩ := Inputs273.comp_facts hO hLc
    obtain ⟨eLK⟩ := Inputs273.nonempty_conj_center_quot K g
    have eS : PSimple 5 (GLBConj g K) ≃* ↥K ⧸ Subgroup.center ↥K :=
      (Lemma1315b.centerQuotEquiv (Inputs273.barOfEquivOfCore hOL)).trans eLK
    obtain ⟨hSs, hSna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hLc
    haveI : IsSimpleGroup (PSimple 5 (GLBConj g K)) := hSs
    have hap5 : a ^ 5 = 1 := hA.2 a ha
    have hap := Inputs273.isPGroup_zpowers_of_pow hap5
    have hI := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp haL hap hJL
    obtain ⟨eJI⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp haL hap hJL
    refine (Inputs123a.isLocallyOTwoBalancedWrtP_congr eJI).2 ?_
    by_cases hα1 : CFSG.LocalAnalysis.GLTheoremA.chevAut 5 (GLBConj g K) ⟨a, haL⟩ = 1
    · have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (CFSG.LocalAnalysis.GLTheoremA.chevAut 5 (GLBConj g K) ⟨a, haL⟩) = ⊤ := by
        rw [hα1]
        ext x
        simp [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
      rw [hfix] at hI
      obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hSna hI
      exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr (e1.trans eS)).2 hO2K
    · exfalso
      have hsolv := CFSG.HardMathSupport.Dickson.Bal207.excSz_isSolvable_fixSubgroup (eS.trans e)
        (CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 5 _ haL hap5) hα1
      exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable hsolv hI
  · obtain ⟨e'⟩ := Inputs273.nonempty_pSimple_equiv_of_not_mem_normalizer hp (by norm_num) hO hK hA ha ha1
      haN hJ
    exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr e').2 hO2K

end Suzuki

section Core


variable {X : Type} [Group X] [Finite X]

theorem chevQ_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : GLAPComponent p ⊤ K) (hKh : CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K)
    (hT : Inputs273.TypeChevQ p (↥K ⧸ Subgroup.center ↥K)) {E : Subgroup X} (hE : IsSCp p ⊤ E)
    (hE3 : 3 ≤ CFSG.Open.pRank p E) (hKΓ : ¬ K ≤ GLBCore p 2 E) (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hC1 : CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1)
    (hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
      5 ≤ p ∧ (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) :
    (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 5 ∧ Subgroup.center ↥K = ⊥ ∧ ∃ hv : (TauCeti.LieTypeIndex.suzuki 2).Valid,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hOK⟩ := Inputs273.comp_facts hO hK
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  have hperf : commutator ↥K = ⊤ := hq.1
  obtain ⟨d, ⟨e⟩, hpd⟩ := exists_index_of_typeChevQ hT
  by_cases hm3 : p = 3 ∧ CFSG.Open.pRank p E = 3
  · exact Or.inl hm3
  have hGM := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hZp : IsPGroup p ↥(Subgroup.center ↥K) := Inputs273.isPGroup_center_of_core hp hOK
  have hcyc : IsCyclic ↥(Subgroup.center ↥K) :=
    isCyclic_center CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hp hp2 hq hOK e hpd
  have hCel : IsElemAbelian p (E ⊓ Subgroup.centralizer (K : Set X)) :=
    CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hCc : Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) = p := by
    rw [Inputs27.card_eq_pow_pRank hp hCel, hC1, pow_one]
  have hC0 : E ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := Inputs273.ne_bot_of_pRank_eq_one hp hC1
  have hEc : Nat.card E = p ^ CFSG.Open.pRank p E := Inputs27.card_eq_pow_pRank hp hE.2.1
  have hstab : GL83.CompFam.stab E K = E := inf_eq_left.2 hN
  obtain ⟨E₂, hE₂N, hE₂C, hE₂c⟩ := InputsSeitz3.exists_faithful hp hE.2.1 (k := 2) (by
    rw [hstab]
    show p ^ 2 * Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card E
    rw [hCc, hEc, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos hE3)
  have hE₂E : E₂ ≤ E := hE₂N.trans inf_le_left
  have hZbot : ¬ p ∣ Nat.card ↥(Subgroup.center ↥K) → Subgroup.center ↥K = ⊥ := fun h => by
    by_contra hZ
    exact h (InputsSeitz6.dvd_card_of_isPGroup hZp hZ)
  by_cases hnd : CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1
  swap
  · exact absurd (le_glbCore_of_plane CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hp hp2 hE hN hq
      hcyc hZp hC0 e hpd hnd hE₂E hE₂C hE₂c) hKΓ
  rcases hnd with ⟨rfl, ⟨q, hq2, hq3, hdq⟩ | ⟨q, hq2, hq3, hdq⟩ | ⟨q, hq2, hq1, hdq⟩ |
      ⟨q, hq2, hq1, hdq | hdq⟩ | hdq⟩ | ⟨rfl, hdq | hdq⟩
  ·
    exfalso
    apply hT.2.1
    refine Or.inr ⟨.lie d, ?_, ⟨e⟩⟩
    obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq2, hq3]
  ·
    exfalso
    have h := (hA2 (InputsSeitz3.pRank_mulAut_le_two_of_l34 hperf
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index d q hdq ⟨hq2, hq3⟩ e))).1
    omega
  ·
    exfalso
    apply hT.2.1
    refine Or.inr ⟨.lie d, ?_, ⟨e⟩⟩
    obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev, hq2, hq1]
  ·
    have hm4 : 4 ≤ CFSG.Open.pRank 3 E := by
      by_contra h
      exact hm3 ⟨rfl, by omega⟩
    have hZ : Subgroup.center ↥K = ⊥ := hZbot fun hdvd => by
      have hc := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp hp2 hq d e hpd hdvd
      rw [hdq] at hc
      exact hc
    have h27 : 3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card E := by
      rw [hCc, hEc, ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hm4
    obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    exact absurd (le_glbCore_of_spTwo hE hN hC0 h27 hZ le_rfl hq2 hq1
      ((InputsSeitz3.equivCenterQuot hZ).trans e)) hKΓ
  ·
    have hm4 : 4 ≤ CFSG.Open.pRank 3 E := by
      by_contra h
      exact hm3 ⟨rfl, by omega⟩
    have hZ : Subgroup.center ↥K = ⊥ := hZbot fun hdvd => by
      have hc := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp hp2 hq d e hpd hdvd
      rw [hdq] at hc
      exact hc
    have h27 : 3 ^ 3 * Nat.card ↥(E ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card E := by
      rw [hCc, hEc, ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hm4
    obtain ⟨d0, hv⟩ := d
    simp only at hdq
    subst hdq
    exact absurd (le_glbCore_of_spTwo hE hN hC0 h27 hZ (by norm_num) hq2 hq1
      ((InputsSeitz3.equivCenterQuot hZ).trans e)) hKΓ
  ·
    exfalso
    have h := (hA2 ((InputsSeitz5.pRank_mulAut_le_quot hp hperf).trans
      (InputsSeitz5.pRank_three_mulAut_le_two_of_tits d hdq e))).1
    omega
  ·
    exact (false_of_tits_five hGM hq hOK hdq e hA2).elim
  ·
    refine Or.inr ⟨rfl, hZbot fun hdvd => ?_, ?_⟩
    · have hc := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp hp2 hq d e hpd hdvd
      rw [hdq] at hc
      exact hc
    · obtain ⟨d0, hv⟩ := d
      simp only at hdq
      subst hdq
      exact ⟨hv, ⟨e⟩⟩

theorem input27_3ChevQ_holds : Inputs273.Input27_3ChevQ := by
  intro p hp hp2 X _ _ _ hO K hK hKh hT E A hE hA' hEA _ hr _ hKΓ hN hC1 _ hA2
  have hE3 := Inputs27.three_le_pRank_of_scp hp hE hA' hEA hr.ge
  rcases chevQ_core hp hp2 hO hK hKh hT hE hE3 hKΓ hN hC1 (fun h => ⟨(hA2 h).1, (hA2 h).2.2.2⟩) with
    ⟨rfl, h3⟩ | ⟨rfl, -, hv, ⟨e⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩))))
  · obtain ⟨-, hOK⟩ := Inputs273.comp_facts hO hK
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isCompLocallyBalanced_sz32 A hKh.1 hOK e))))))

theorem input27_4ChevQ_holds : Inputs273.Input27_4ChevQ := by
  intro p hp hp2 X _ _ _ hO K hK hKh hT E A hE hA' hEA _ hr _ _ hKΓ hN hC1 _ hA2
  have hE3 := Inputs27.three_le_pRank_of_scp hp hE hA' hEA hr
  rcases chevQ_core hp hp2 hO hK hKh hT hE hE3 hKΓ hN hC1 (fun h => ⟨(hA2 h).1, (hA2 h).2.2.2⟩) with
    ⟨rfl, h3⟩ | ⟨rfl, -, hv, ⟨e⟩⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩))))
  · exact Or.inr (Or.inr (Or.inl fun a ha ha1 J hJ => Or.inl (sz32_down hO hK e hA'.2.1 ha ha1 hJ)))

theorem input27_34ChevQ_holds : Inputs273.Input27_3ChevQ ∧ Inputs273.Input27_4ChevQ :=
  ⟨input27_3ChevQ_holds, input27_4ChevQ_holds⟩

end Core

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d

end
