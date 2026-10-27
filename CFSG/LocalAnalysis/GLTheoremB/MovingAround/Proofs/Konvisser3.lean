module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input31
public import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section K3Basic

variable {G : Type} [Group G]

theorem k3_comm {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (isMulCommutative_iff.mp hE.1 ⟨x, hx⟩ ⟨y, hy⟩)

def K3Cent (C : Subgroup G) (z : G) : Prop := ∀ d ∈ C, d * z = z * d

theorem k3Cent_one (C : Subgroup G) : K3Cent C 1 := fun d _ => by simp

theorem k3Cent_mul {C : Subgroup G} {z w : G} (hz : K3Cent C z) (hw : K3Cent C w) :
    K3Cent C (z * w) := by
  intro d hd
  calc d * (z * w) = (d * z) * w := by rw [mul_assoc]
    _ = (z * d) * w := by rw [hz d hd]
    _ = z * (d * w) := by rw [mul_assoc]
    _ = z * (w * d) := by rw [hw d hd]
    _ = z * w * d := by rw [mul_assoc]

theorem k3Cent_inv {C : Subgroup G} {z : G} (hz : K3Cent C z) : K3Cent C z⁻¹ := by
  intro d hd
  have h := hz d hd
  calc d * z⁻¹ = z⁻¹ * (z * d) * z⁻¹ := by group
    _ = z⁻¹ * (d * z) * z⁻¹ := by rw [h]
    _ = z⁻¹ * d := by group

theorem k3Cent_conj {C : Subgroup G} {h z : G} (hh : ∀ d ∈ C, h⁻¹ * d * h ∈ C)
    (hz : K3Cent C z) : K3Cent C (h * z * h⁻¹) := by
  intro d hd
  have h1 := hz _ (hh d hd)
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [h1]
    _ = h * z * h⁻¹ * d := by group

theorem k3_conj_mem_of_normalizer {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) : ∀ d ∈ C, g⁻¹ * d * g ∈ C := by
  intro d hd
  refine (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * d * g)).mpr ?_
  convert hd using 1
  group

end K3Basic

section K3Class2

variable {G : Type} [Group G]

theorem k3_pow_mul_of_class_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y c : G}
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hyx : y * x = x * y * c) (hcx : Commute c x)
    (hcy : Commute c y) : (x * y) ^ p = 1 := by
  have hcyn : ∀ n : ℕ, Commute c (y ^ n) := fun n => hcy.pow_right n
  have hi : ∀ n : ℕ, y ^ n * x = x * y ^ n * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
        _ = y * (x * y ^ n * c ^ n) := by rw [ih]
        _ = (y * x) * y ^ n * c ^ n := by group
        _ = x * y * c * y ^ n * c ^ n := by rw [hyx]
        _ = x * y * (c * y ^ n) * c ^ n := by group
        _ = x * y * (y ^ n * c) * c ^ n := by rw [(hcyn n).eq]
        _ = x * y ^ (n + 1) * c ^ (n + 1) := by rw [pow_succ y n, pow_succ c n]; group
  have hii : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * c ^ (n.choose 2) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hce : Commute (c ^ (n.choose 2)) x := (hcx.pow_left _)
      have hcey : Commute (c ^ (n.choose 2)) y := (hcy.pow_left _)
      have hcn : Commute (c ^ n * c ^ (n.choose 2)) y :=
        (hcy.pow_left n).mul_left (hcy.pow_left _)
      have hchoose : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
        _ = x ^ n * y ^ n * c ^ (n.choose 2) * (x * y) := by rw [ih]
        _ = x ^ n * y ^ n * (c ^ (n.choose 2) * x) * y := by group
        _ = x ^ n * y ^ n * (x * c ^ (n.choose 2)) * y := by rw [hce.eq]
        _ = x ^ n * (y ^ n * x) * c ^ (n.choose 2) * y := by group
        _ = x ^ n * (x * y ^ n * c ^ n) * c ^ (n.choose 2) * y := by rw [hi n]
        _ = x ^ (n + 1) * y ^ n * (c ^ n * c ^ (n.choose 2)) * y := by
              rw [pow_succ]; group
        _ = x ^ (n + 1) * y ^ n * ((c ^ n * c ^ (n.choose 2)) * y) := by group
        _ = x ^ (n + 1) * y ^ n * (y * (c ^ n * c ^ (n.choose 2))) := by rw [hcn.eq]
        _ = x ^ (n + 1) * (y ^ n * y) * (c ^ n * c ^ (n.choose 2)) := by group
        _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + (n.choose 2)) := by
              rw [pow_succ y n, pow_add]; group
        _ = x ^ (n + 1) * y ^ (n + 1) * c ^ ((n + 1).choose 2) := by rw [hchoose]
  have hc1 : c ^ p = 1 := by
    have h := hi p
    rw [hyp, one_mul] at h
    simpa using h.symm
  rw [hii p, hxp, hyp, one_mul, one_mul]
  obtain ⟨k, hk⟩ := Nat.Prime.dvd_choose_self hp (by norm_num : (2 : ℕ) ≠ 0)
    (by have := hp.two_le; omega : 2 < p)
  rw [hk, pow_mul, hc1, one_pow]

def k3T {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (C : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ C ∧ x ^ p = 1 ∧ ∀ c ∈ C, K3Cent C (c * x * c⁻¹ * x⁻¹)}
  one_mem' := ⟨C.one_mem, one_pow p, fun c _ => by simpa using k3Cent_one C⟩
  mul_mem' := by
    rintro x y ⟨hxC, hxp, hxc⟩ ⟨hyC, hyp, hyc⟩
    refine ⟨C.mul_mem hxC hyC, ?_, ?_⟩
    ·
      have hz0 := hyc x⁻¹ (C.inv_mem hxC)
      rw [inv_inv] at hz0
      have hconj := k3Cent_conj (h := y⁻¹)
        (fun d hd => by rw [inv_inv]; exact C.mul_mem (C.mul_mem hyC hd) (C.inv_mem hyC)) hz0
      have hc0 : K3Cent C (y⁻¹ * x⁻¹ * y * x) := by
        have e : y⁻¹ * x⁻¹ * y * x = y⁻¹ * (x⁻¹ * y * x * y⁻¹) * y⁻¹⁻¹ := by group
        rw [e]; exact hconj
      have hyx : y * x = x * y * (y⁻¹ * x⁻¹ * y * x) := by group
      exact k3_pow_mul_of_class_two hp hp2 hxp hyp hyx (hc0 x hxC).symm (hc0 y hyC).symm
    · intro c hc
      have e : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
          (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact k3Cent_mul (hxc c hc)
        (k3Cent_conj (h := x) (fun d hd => C.mul_mem (C.mul_mem (C.inv_mem hxC) hd) hxC)
          (hyc c hc))
  inv_mem' := by
    rintro x ⟨hxC, hxp, hxc⟩
    refine ⟨C.inv_mem hxC, by rw [inv_pow, hxp, inv_one], ?_⟩
    intro c hc
    have e : c * x⁻¹ * c⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
    rw [e]
    exact k3Cent_conj (h := x⁻¹)
      (fun d hd => by rw [inv_inv]; exact C.mul_mem (C.mul_mem hxC hd) (C.inv_mem hxC))
      (k3Cent_inv (hxc c hc))

theorem mem_k3T {p : ℕ} {hp : p.Prime} {hp2 : p ≠ 2} {C : Subgroup G} {x : G} :
    x ∈ k3T hp hp2 C ↔ x ∈ C ∧ x ^ p = 1 ∧ ∀ c ∈ C, K3Cent C (c * x * c⁻¹ * x⁻¹) := Iff.rfl

theorem k3T_normalizer {p : ℕ} {hp : p.Prime} {hp2 : p ≠ 2} {C P : Subgroup G}
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) :
    P ≤ Subgroup.normalizer ((k3T hp hp2 C : Subgroup G) : Set G) := by
  have hconj : ∀ g ∈ P, ∀ n ∈ k3T hp hp2 C, g * n * g⁻¹ ∈ k3T hp hp2 C := by
    intro g hg n hn
    obtain ⟨hnC, hnp, hnc⟩ := mem_k3T.mp hn
    have hgn : g ∈ Subgroup.normalizer (C : Set G) := hPC hg
    refine mem_k3T.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgn n).mp hnC, ?_, ?_⟩
    · rw [conj_pow, hnp, mul_one, mul_inv_cancel]
    · intro c hc
      have e : c * (g * n * g⁻¹) * c⁻¹ * (g * n * g⁻¹)⁻¹ =
          g * ((g⁻¹ * c * g) * n * (g⁻¹ * c * g)⁻¹ * n⁻¹) * g⁻¹ := by group
      rw [e]
      have hc' : g⁻¹ * c * g ∈ C := k3_conj_mem_of_normalizer hgn c hc
      exact k3Cent_conj (h := g) (k3_conj_mem_of_normalizer hgn) (hnc _ hc')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hconj g hg n hn
  · intro hn
    have := hconj g⁻¹ (P.inv_mem hg) _ hn
    convert this using 1
    group

end K3Class2

section K3Quot

variable {H : Type} [Group H] [Finite H]

theorem k3_quot_isPGroup {p : ℕ} (hp : IsPGroup p H) (N : Subgroup H) [N.Normal] :
    IsPGroup p (H ⧸ N) := by
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, hk⟩ := hp h
  exact ⟨k, by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]⟩

theorem k3_card_map_mk (N M : Subgroup H) [N.Normal] (hNM : N ≤ M) :
    Nat.card (M.map (QuotientGroup.mk' N)) * Nat.card N = Nat.card M := by
  have hi : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmap : (M.map (QuotientGroup.mk' N)).index = M.index :=
    Subgroup.index_map_eq M (QuotientGroup.mk'_surjective N)
      (by rw [QuotientGroup.ker_mk']; exact hNM)
  have e1 := Subgroup.card_mul_index M
  have e2 := Subgroup.card_mul_index (M.map (QuotientGroup.mk' N))
  have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hmap] at e2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  calc Nat.card (M.map (QuotientGroup.mk' N)) * Nat.card N * M.index
      = Nat.card (M.map (QuotientGroup.mk' N)) * M.index * Nat.card N := by ring
    _ = Nat.card (H ⧸ N) * Nat.card N := by rw [e2]
    _ = Nat.card H := e3.symm
    _ = Nat.card M * M.index := e1.symm

theorem k3_card_comap_mk (N : Subgroup H) [N.Normal] (K : Subgroup (H ⧸ N)) :
    Nat.card (K.comap (QuotientGroup.mk' N)) = Nat.card K * Nat.card N := by
  have hi : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmap : (K.comap (QuotientGroup.mk' N)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective N)
  have e1 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' N))
  have e2 := Subgroup.card_mul_index K
  have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hmap] at e1
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi)
  calc Nat.card (K.comap (QuotientGroup.mk' N)) * K.index
      = Nat.card H := e1
    _ = Nat.card (H ⧸ N) * Nat.card N := e3
    _ = Nat.card K * K.index * Nat.card N := by rw [← e2]
    _ = Nat.card K * Nat.card N * K.index := by ring

end K3Quot

section K3Central

variable {H : Type} [Group H] [Finite H]

theorem k3_central_of_card_eq {p : ℕ} [hp : Fact p.Prime] (hH : IsPGroup p H)
    (N : Subgroup H) [N.Normal] (hcard : Nat.card N = p) : N ≤ Subgroup.center H := by
  classical
  have hG : IsPGroup p (ConjAct H) := hH.of_equiv ConjAct.toConjAct
  have hmod := hG.card_modEq_card_fixedPoints N
  have hone : (1 : N) ∈ MulAction.fixedPoints (ConjAct H) N := by
    rw [MulAction.mem_fixedPoints]
    intro g
    ext
    simp [ConjAct.smul_def]
  have hpos : 0 < Nat.card (MulAction.fixedPoints (ConjAct H) N) := by
    haveI : Nonempty (MulAction.fixedPoints (ConjAct H) N) := ⟨⟨1, hone⟩⟩
    exact Nat.card_pos
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints (ConjAct H) N) := by
    have h0 : Nat.card N ≡ 0 [MOD p] := by
      rw [hcard]; exact (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
  have hge : p ≤ Nat.card (MulAction.fixedPoints (ConjAct H) N) := Nat.le_of_dvd hpos hdvd
  intro x hx
  have hxfix : (⟨x, hx⟩ : N) ∈ MulAction.fixedPoints (ConjAct H) N := by
    by_contra hnot
    have hlt := Finite.card_subtype_lt
      (p := fun y : N => y ∈ MulAction.fixedPoints (ConjAct H) N) hnot
    rw [hcard] at hlt
    exact absurd hge (not_le.mpr hlt)
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := (MulAction.mem_fixedPoints.mp hxfix) (ConjAct.toConjAct g)
  have hg' : g * x * g⁻¹ = x := by
    have h2 : ((ConjAct.toConjAct g • (⟨x, hx⟩ : N) : N) : H) = g * x * g⁻¹ := rfl
    rw [hg] at h2
    exact h2.symm
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [hg']

end K3Central

section K3Comm

variable {G : Type} [Group G] [Finite G]

theorem k3_commutator_mem {p : ℕ} [hp : Fact p.Prime] {Q U W C : Subgroup G}
    (hQ : IsPGroup p Q) (hWQ : W ≤ Q) (hUQ : U ≤ Q) (hWU : W ≤ U)
    (hNU : Q ≤ Subgroup.normalizer (U : Set G)) (hNW : Q ≤ Subgroup.normalizer (W : Set G))
    (hUc : Nat.card U = p * Nat.card W) (hCQ : C ≤ Q) :
    ∀ c ∈ C, ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ W := by
  intro c hc u hu
  have hQ' : IsPGroup p ↥Q := hQ
  have hWqn : (W.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWQ).mpr hNW
  have hUqn : (U.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUQ).mpr hNU
  have hWqU : W.subgroupOf Q ≤ U.subgroupOf Q := Subgroup.subgroupOf_mono Q hWU
  have hQbar : IsPGroup p (↥Q ⧸ W.subgroupOf Q) := k3_quot_isPGroup hQ' _
  haveI : Fact (IsPGroup p (↥Q ⧸ W.subgroupOf Q)) := ⟨hQbar⟩
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hcardW : Nat.card (W.subgroupOf Q) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWQ).toEquiv
  have hcardU : Nat.card (U.subgroupOf Q) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
  have hcardUbar : Nat.card ((U.subgroupOf Q).map (QuotientGroup.mk' (W.subgroupOf Q))) = p := by
    have h1 := k3_card_map_mk (W.subgroupOf Q) (U.subgroupOf Q) hWqU
    rw [hcardW, hcardU, hUc] at h1
    exact Nat.eq_of_mul_eq_mul_right hWpos h1
  have hcen := k3_central_of_card_eq hQbar
    ((U.subgroupOf Q).map (QuotientGroup.mk' (W.subgroupOf Q))) hcardUbar
  have hcQ : c ∈ Q := hCQ hc
  have huQ : u ∈ Q := hUQ hu
  have hmem : QuotientGroup.mk' (W.subgroupOf Q) (⟨u, huQ⟩ : ↥Q) ∈
      (U.subgroupOf Q).map (QuotientGroup.mk' (W.subgroupOf Q)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
  have hcomm := (Subgroup.mem_center_iff.mp (hcen hmem)) (QuotientGroup.mk' (W.subgroupOf Q)
    (⟨c, hcQ⟩ : ↥Q))
  have key : QuotientGroup.mk' (W.subgroupOf Q)
      ((⟨c, hcQ⟩ : ↥Q) * (⟨u, huQ⟩ : ↥Q) * (⟨c, hcQ⟩ : ↥Q)⁻¹ * (⟨u, huQ⟩ : ↥Q)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp key)

theorem k3_map_subtype_normalizer {P : Subgroup G} (A : Subgroup P) [A.Normal] :
    P ≤ Subgroup.normalizer ((A.map P.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g : P, ∀ n ∈ A, (g : G) * (n : G) * (g : G)⁻¹ ∈ A.map P.subtype := by
    intro g n hn
    exact Subgroup.mem_map.mpr ⟨g * n * g⁻¹, Subgroup.Normal.conj_mem ‹A.Normal› n hn g, by simp⟩
  intro n
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact key ⟨h, hh⟩ m hm
  · intro hn
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hn
    have h2 : (h⁻¹ : G) * (m : G) * (h⁻¹ : G)⁻¹ ∈ A.map P.subtype :=
      key ⟨h⁻¹, P.inv_mem hh⟩ m hm
    have hmn' : (m : G) = h * n * h⁻¹ := hmn
    have e : (h⁻¹ : G) * (m : G) * (h⁻¹ : G)⁻¹ = n := by
      rw [hmn']
      group
    rw [e] at h2
    exact h2

end K3Comm

section K3Step

variable {G : Type} [Group G] [Finite G]

theorem k3_step {p : ℕ} [hp : Fact p.Prime] {P T W : Subgroup G}
    (hP : IsPGroup p P) (hTP : T ≤ P) (hWP : W ≤ P) (hWT : W ≤ T)
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hlt : W < T) :
    ∃ S : Subgroup G, W ≤ S ∧ S ≤ T ∧ P ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card S = Nat.card W * p := by
  have hP' : IsPGroup p ↥P := hP
  have hWpn : (W.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWP).mpr hPW
  have hTpn : (T.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTP).mpr hPT
  have hPbar : IsPGroup p (↥P ⧸ W.subgroupOf P) := k3_quot_isPGroup hP' _
  haveI : Fact (IsPGroup p (↥P ⧸ W.subgroupOf P)) := ⟨hPbar⟩
  have hTbarn : ((T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))).Normal :=
    Subgroup.Normal.map hTpn _ (QuotientGroup.mk'_surjective _)
  obtain ⟨t, htT, htW⟩ : ∃ t ∈ T, t ∉ W := by
    obtain ⟨t, ht1, ht2⟩ := SetLike.exists_of_lt hlt
    exact ⟨t, ht1, ht2⟩
  have htP : t ∈ P := hTP htT
  have hmemT : QuotientGroup.mk' (W.subgroupOf P) (⟨t, htP⟩ : ↥P) ∈
      (T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htT)
  have hnt : QuotientGroup.mk' (W.subgroupOf P) (⟨t, htP⟩ : ↥P) ≠ 1 := by
    intro h1
    exact htW (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  have hTbarp : IsPGroup p ↥((T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))) :=
    hPbar.to_subgroup _
  haveI hTbar_nt : Nontrivial ↥((T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))) :=
    ⟨⟨⟨_, hmemT⟩, ⟨1, (T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P)) |>.one_mem⟩,
      fun h => hnt (congrArg Subtype.val h)⟩⟩
  obtain ⟨k, hk0, hkc⟩ := hTbarp.nontrivial_iff_card.mp hTbar_nt
  obtain ⟨K, hKn, hKT, hKc⟩ := CFSG.exists_normal_subgroup_card_pow_of_normal
    ((T.subgroupOf P).map (QuotientGroup.mk' (W.subgroupOf P))) hTbarn hkc 1 (by omega)
  have hWpcard : Nat.card (W.subgroupOf P) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv
  set S₀ : Subgroup P := K.comap (QuotientGroup.mk' (W.subgroupOf P)) with hS₀
  have hS₀n : S₀.Normal := inferInstance
  have hWS₀ : W.subgroupOf P ≤ S₀ := by
    intro w hw
    rw [hS₀, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hw]
    exact K.one_mem
  have hS₀T : S₀ ≤ T.subgroupOf P := by
    intro x hx
    have hx' : QuotientGroup.mk' (W.subgroupOf P) x ∈ K := hx
    obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.mp (hKT hx')
    have hyx' : (QuotientGroup.mk' (W.subgroupOf P)) y = (QuotientGroup.mk' (W.subgroupOf P)) x :=
      hyx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx'
    have hWT' : W.subgroupOf P ≤ T.subgroupOf P := Subgroup.subgroupOf_mono P hWT
    have hmem : y⁻¹ * x ∈ T.subgroupOf P := hWT' hyx'
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact (T.subgroupOf P).mul_mem hyT hmem
  have hcardS₀ : Nat.card S₀ = Nat.card W * p := by
    rw [hS₀, k3_card_comap_mk (W.subgroupOf P) K, hWpcard, hKc, pow_one, mul_comm]
  refine ⟨S₀.map P.subtype, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact Subgroup.mem_map.mpr ⟨⟨w, hWP hw⟩, hWS₀ (Subgroup.mem_subgroupOf.mpr hw), rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hS₀T hy)
  · exact k3_map_subtype_normalizer S₀
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hcardS₀]

end K3Step

section K3Complement

theorem k3_complement_comm {A : Type} [CommGroup A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hexp : ∀ a : A, a ^ p = 1) (K : Subgroup A) :
    ∃ X : Subgroup A, X ⊓ K = ⊥ ∧ X ⊔ K = ⊤ := by
  classical
  obtain ⟨X, hXS, hXmax⟩ := Set.exists_max_image {X : Subgroup A | X ⊓ K = ⊥}
    (fun X : Subgroup A => Nat.card X) (Set.toFinite _) ⟨⊥, by simp⟩
  refine ⟨X, hXS, ?_⟩
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ X ⊔ K := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun a _ => h a)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hX'S : (X ⊔ Subgroup.zpowers a) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup.mp hy1
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hai : a ^ i ∈ X ⊔ K := by
      have e : a ^ i = x⁻¹ * (x * a ^ i) := by group
      rw [e]
      exact (X ⊔ K).mul_mem (Subgroup.mem_sup_left (X.inv_mem hx))
        (Subgroup.mem_sup_right hy2)
    have hpi : (p : ℤ) ∣ i := by
      by_contra hnd
      have hcop : IsCoprime (p : ℤ) i := (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hnd
      obtain ⟨u, v, huv⟩ := hcop
      apply ha
      have e : a = (a ^ i) ^ v := by
        calc a = a ^ (u * p + v * i) := by rw [huv, zpow_one]
          _ = (a ^ (p : ℤ)) ^ u * (a ^ i) ^ v := by
              rw [zpow_add, mul_comm u (p : ℤ), zpow_mul, mul_comm v i, zpow_mul]
          _ = (a ^ i) ^ v := by
              rw [zpow_natCast, hexp a, one_zpow, one_mul]
      rw [e]
      exact (X ⊔ K).zpow_mem hai v
    obtain ⟨m, rfl⟩ := hpi
    have hap : a ^ ((p : ℤ) * m) = 1 := by
      rw [zpow_mul, zpow_natCast, hexp a, one_zpow]
    have hxK : x ∈ K := by
      rw [hap, mul_one] at hy2
      exact hy2
    have hxX : x ∈ X ⊓ K := ⟨hx, hxK⟩
    rw [hXS] at hxX
    rw [hap, mul_one]
    exact hxX
  have hlt : X < X ⊔ Subgroup.zpowers a := by
    refine lt_of_le_of_ne le_sup_left (fun h => ha ?_)
    have : a ∈ X ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
    rw [← h] at this
    exact Subgroup.mem_sup_left this
  have hle := hXmax (X ⊔ Subgroup.zpowers a) hX'S
  exact absurd hle (not_le.mpr (Subgroup.card_lt_of_lt hlt))

end K3Complement

section K3Rest

variable {G : Type} [Group G] [Finite G]

theorem k3_comm_of_index {p : ℕ} [hp : Fact p.Prime] {S W : Subgroup G} (hWS : W ≤ S)
    (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w) (hS : Nat.card S = Nat.card W * p) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  classical
  have hWn : (W.subgroupOf S).Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ W := Subgroup.mem_subgroupOf.mp hn
    have := hWc (n : G) hn' (g : G) g.2
    have e : (g : G) * (n : G) * (g : G)⁻¹ = n := by
      rw [← this]; group
    refine Subgroup.mem_subgroupOf.mpr ?_
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ W
    rw [e]; exact hn'
  have hcen : W.subgroupOf S ≤ Subgroup.center S := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    have := hWc (w : G) (Subgroup.mem_subgroupOf.mp hw) (g : G) g.2
    exact Subtype.ext this.symm
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hWsc : Nat.card (W.subgroupOf S) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWS).toEquiv
  haveI : (W.subgroupOf S).Normal := hWn
  have hcard : Nat.card (S ⧸ W.subgroupOf S) = p := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (W.subgroupOf S)
    rw [hS, hWsc] at h1
    apply Nat.eq_of_mul_eq_mul_right hWpos
    rw [← h1, mul_comm]
  haveI : IsCyclic (S ⧸ W.subgroupOf S) := isCyclic_of_prime_card hcard
  intro x hx y hy
  have := commutative_of_cyclic_center_quotient (QuotientGroup.mk' (W.subgroupOf S))
    (by rw [QuotientGroup.ker_mk']; exact hcen) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

end K3Rest

section K3Rest2

variable {G : Type} [Group G] [Finite G]

theorem k3_mem_sup_zpowers {W : Subgroup G} {x : G} (hwx : ∀ w ∈ W, w * x = x * w) {a : G}
    (ha : a ∈ W ⊔ Subgroup.zpowers x) : ∃ w ∈ W, ∃ k : ℤ, a = w * x ^ k := by
  have hcomm : ∀ (w : G), w ∈ W → ∀ k : ℤ, x ^ k * w = w * x ^ k := fun w hw k =>
    ((show Commute w x from hwx w hw).zpow_right k).eq.symm
  let H : Subgroup G :=
    { carrier := {a | ∃ w ∈ W, ∃ k : ℤ, a = w * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨w1, hw1, k1, rfl⟩ ⟨w2, hw2, k2, rfl⟩
        refine ⟨w1 * w2, W.mul_mem hw1 hw2, k1 + k2, ?_⟩
        calc w1 * x ^ k1 * (w2 * x ^ k2) = w1 * (x ^ k1 * w2) * x ^ k2 := by group
          _ = w1 * (w2 * x ^ k1) * x ^ k2 := by rw [hcomm w2 hw2 k1]
          _ = w1 * w2 * x ^ (k1 + k2) := by rw [zpow_add]; group
      one_mem' := ⟨1, W.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨w, hw, k, rfl⟩
        refine ⟨w⁻¹, W.inv_mem hw, -k, ?_⟩
        rw [zpow_neg, mul_inv_rev]
        exact (((show Commute w (x ^ k) from (hcomm w hw k).symm).inv_inv).eq).symm }
  have hle : W ⊔ Subgroup.zpowers x ≤ H :=
    sup_le (fun w hw => ⟨w, hw, 0, by simp⟩)
      (fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ⟨1, W.one_mem, k, by simp⟩)
  exact hle ha

theorem k3_exists_complement {p : ℕ} [hp : Fact p.Prime] {E K : Subgroup G}
    (hE : IsElemAbelian p E) (hK : K ≤ E) :
    ∃ X : Subgroup G, X ≤ E ∧ (∀ x ∈ X, x ∈ K → x = 1) ∧
      Nat.card X * Nat.card K = Nat.card E := by
  classical
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => isMulCommutative_iff.mp hE.1 a b }
  have hexp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hE.2 a.1 a.2)
  obtain ⟨X', hX'K, hX'top⟩ := k3_complement_comm hexp (K.subgroupOf E)
  refine ⟨X'.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx hxK
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyK : y ∈ K.subgroupOf E := Subgroup.mem_subgroupOf.mpr hxK
    have hmem : y ∈ X' ⊓ K.subgroupOf E := ⟨hy, hyK⟩
    rw [hX'K, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  · have hcent : X' ≤ Subgroup.centralizer ((K.subgroupOf E : Subgroup E) : Set E) := by
      intro y _
      exact Subgroup.mem_centralizer_iff.mpr (fun z _ => mul_comm z y)
    have hprod := input31_card_sup_mul_card_inf hcent
    rw [hX'top, hX'K, Subgroup.card_top, Subgroup.card_bot, mul_one] at hprod
    have hKc : Nat.card (K.subgroupOf E) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
    rw [Subgroup.card_map_of_injective E.subtype_injective, ← hKc]
    exact hprod.symm

theorem k3_exists_normal_lt {p : ℕ} [hp : Fact p.Prime] {P Y : Subgroup G} (hP : IsPGroup p P)
    (hYP : Y ≤ P) (hYne : Y ≠ P) :
    ∃ M : Subgroup G, Y ≤ M ∧ M ≤ P ∧ P ≤ Subgroup.normalizer (M : Set G) ∧
      Nat.card M < Nat.card P := by
  have hP' : IsPGroup p ↥P := hP
  haveI : Group.IsNilpotent ↥P := hP'.isNilpotent
  set Y' : Subgroup P := Y.subgroupOf P with hY'
  have hY'ne : Y' ≠ ⊤ := by
    intro h
    apply hYne
    apply le_antisymm hYP
    intro g hg
    have hmem : (⟨g, hg⟩ : P) ∈ Y' := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨M', hM'S, hM'max⟩ := Set.exists_max_image {M : Subgroup P | Y' ≤ M ∧ M ≠ ⊤}
    (fun M : Subgroup P => Nat.card M) (Set.toFinite _) ⟨Y', le_rfl, hY'ne⟩
  obtain ⟨hYM', hM'ne⟩ := hM'S
  have hcoat : IsCoatom M' := by
    refine ⟨hM'ne, fun b hb => ?_⟩
    by_contra hbne
    have hbS : b ∈ {M : Subgroup P | Y' ≤ M ∧ M ≠ ⊤} := ⟨hYM'.trans hb.le, hbne⟩
    have hle := hM'max b hbS
    exact absurd (Subgroup.card_lt_of_lt hb) (not_lt.mpr hle)
  have hidx : M'.index = p := (IsPGroup.isCoatom_iff_index_eq_prime hP').mp hcoat
  haveI : M'.Normal := Subgroup.NormalizerCondition.normal_of_coatom M' (Group.normalizerCondition_of_isNilpotent (G := ↥P)) hcoat
  refine ⟨M'.map P.subtype, ?_, Subgroup.map_subtype_le _, k3_map_subtype_normalizer M', ?_⟩
  · intro y hy
    exact Subgroup.mem_map.mpr ⟨⟨y, hYP hy⟩, hYM' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  · rw [Subgroup.card_map_of_injective P.subtype_injective]
    have e1 := Subgroup.card_mul_index M'
    rw [hidx] at e1
    have hpos : 0 < Nat.card M' := Nat.card_pos
    have hp2 : 2 ≤ p := hp.out.two_le
    rw [← e1]
    nlinarith

theorem k3_normalizes_inter {P Q W : Subgroup G} (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hPW : P ≤ Subgroup.normalizer (W : Set G)) :
    P ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  have hkey : ∀ g ∈ P, ∀ x ∈ Q ⊓ Subgroup.centralizer (W : Set G),
      g * x * g⁻¹ ∈ Q ⊓ Subgroup.centralizer (W : Set G) := by
    intro g hg x hx
    obtain ⟨hxQ, hxc⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hPQ hg) x).mp hxQ,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hPW (P.inv_mem hg)) w).mp hw
    have hxw := Subgroup.mem_centralizer_iff.mp hxc _ hw'
    have e1 : w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
    calc w * (g * x * g⁻¹) = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ * (g * x * g⁻¹) := by rw [← e1]
      _ = g * ((g⁻¹ * w * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [hxw]
      _ = (g * x * g⁻¹) * (g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹) := by group
      _ = (g * x * g⁻¹) * w := by rw [← e1]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hkey h hh n hn
  · intro hn
    have := hkey h⁻¹ (P.inv_mem hh) _ hn
    convert this using 1
    group

theorem k3_sup_zpowers {p : ℕ} [hp : Fact p.Prime] {W : Subgroup G} {x : G} (hW : IsPPlane p W)
    (hxC : x ∈ Subgroup.centralizer (W : Set G)) (hxp : x ^ p = 1) (hxW : x ∉ W) :
    IsElemAbelian p (W ⊔ Subgroup.zpowers x) ∧
      Nat.card (W ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 := by
  have hwx : ∀ w ∈ W, w * x = x * w := fun w hw => Subgroup.mem_centralizer_iff.mp hxC w hw
  have hxne : x ≠ 1 := fun h => hxW (h ▸ W.one_mem)
  have hord : orderOf x = p := orderOf_eq_prime hxp hxne
  have hzc : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hord]
  have hcentr : W ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((show Commute w x from hwx w hw).zpow_right k).eq.symm
  have hint : W ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (W ⊓ Subgroup.zpowers x : Subgroup G) ∣ p := by
      rw [← hzc]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hEq : W ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hzc, h1])
      have hxin : x ∈ W ⊓ Subgroup.zpowers x := by
        rw [hEq]; exact Subgroup.mem_zpowers x
      exact hxW hxin.1
  have hprod := input31_card_sup_mul_card_inf hcentr
  rw [hint, Subgroup.card_bot, hzc, hW.2, mul_one] at hprod
  have hcardY : Nat.card (W ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 := by
    rw [hprod]; ring
  have hxzp : ∀ k : ℤ, (x ^ k) ^ p = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcomm : ∀ a ∈ W ⊔ Subgroup.zpowers x, ∀ b ∈ W ⊔ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨w1, hw1, k1, rfl⟩ := k3_mem_sup_zpowers hwx ha
    obtain ⟨w2, hw2, k2, rfl⟩ := k3_mem_sup_zpowers hwx hb
    have c12 : Commute w1 w2 := k3_comm hW.1 hw1 hw2
    have cw1x2 : Commute w1 (x ^ k2) := (show Commute w1 x from hwx w1 hw1).zpow_right k2
    have cxw2 : Commute (x ^ k1) w2 := ((show Commute w2 x from hwx w2 hw2).symm).zpow_left k1
    have cxx : Commute (x ^ k1) (x ^ k2) := (Commute.refl x).zpow_zpow k1 k2
    have hA : Commute w1 (w2 * x ^ k2) := c12.mul_right cw1x2
    have hB : Commute (x ^ k1) (w2 * x ^ k2) := cxw2.mul_right cxx
    exact hA.mul_left hB
  have hexpY : ∀ a ∈ W ⊔ Subgroup.zpowers x, a ^ p = 1 := by
    intro a ha
    obtain ⟨w1, hw1, k1, rfl⟩ := k3_mem_sup_zpowers hwx ha
    rw [((show Commute w1 x from hwx w1 hw1).zpow_right k1).mul_pow, hW.1.2 w1 hw1, hxzp k1,
      one_mul]
  exact ⟨⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)), hexpY⟩,
    hcardY⟩

end K3Rest2

section K3Klem

variable {G : Type} [Group G] [Finite G]

theorem k3_klem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ n : ℕ, ∀ P Q W Y : Subgroup G, Nat.card P + Nat.card Q ≤ n → IsPGroup p ↥P → Q ≤ P →
      P ≤ Subgroup.normalizer (Q : Set G) → W ≤ Q → P ≤ Subgroup.normalizer (W : Set G) →
      IsPPlane p W → Y ≤ Q → IsElemAbelian p Y → Nat.card Y = p ^ 3 → W ≤ Y →
      ∃ V : Subgroup G, V ≤ Q ∧ P ≤ Subgroup.normalizer (V : Set G) ∧ IsElemAbelian p V ∧
        Nat.card V = p ^ 3 ∧ W ≤ V := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q W Y hn hP hQP hPQ hWQ hPW hW hYQ hY hYc hWY
  set Q₁ : Subgroup G := Subgroup.closure {x | ∃ g ∈ P, ∃ y ∈ Y, x = g * y * g⁻¹} with hQ₁
  have hgen : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hPQ hg) y).mp (hYQ hy)
  have hQ₁Q : Q₁ ≤ Q := by
    rw [hQ₁]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨g, hg, y, hy, rfl⟩
    exact hgen g hg y hy
  have hYQ₁ : Y ≤ Q₁ := by
    intro y hy
    rw [hQ₁]
    exact Subgroup.subset_closure ⟨1, P.one_mem, y, hy, by simp⟩
  have hconj : ∀ h ∈ P, ∀ x ∈ Q₁, h * x * h⁻¹ ∈ Q₁ := by
    intro h hh x hx
    have hsub : Q₁ ≤ Subgroup.comap (MulAut.conj h).toMonoidHom Q₁ := by
      rw [hQ₁]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨g, hg, y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      apply Subgroup.subset_closure
      refine ⟨h * g, P.mul_mem hh hg, y, hy, ?_⟩
      show h * (g * y * g⁻¹) * h⁻¹ = h * g * y * (h * g)⁻¹
      group
    exact hsub hx
  have hPQ₁ : P ≤ Subgroup.normalizer (Q₁ : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hconj h hh n hn
    · intro hn
      have := hconj h⁻¹ (P.inv_mem hh) _ hn
      convert this using 1
      group
  by_cases hlt : Q₁ = Q
  ·
    by_cases hYP : Y = P
    · exact ⟨Y, hYQ, by rw [hYP]; exact Subgroup.le_normalizer, hY, hYc, hWY⟩
    · have hYP' : Y ≤ P := hYQ.trans hQP
      obtain ⟨M, hYM, hMP, hPM, hcardM⟩ := k3_exists_normal_lt hP hYP' hYP
      have hQM : Q ≤ M := by
        rw [← hlt, hQ₁]
        apply (Subgroup.closure_le _).mpr
        rintro x ⟨g, hg, y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hPM hg) y).mp (hYM hy)
      have hcardQ : Nat.card Q < Nat.card P :=
        lt_of_le_of_lt (Subgroup.card_le_of_le hQM) hcardM
      have hQp : IsPGroup p ↥Q := hP.to_le hQP
      obtain ⟨U, hUQ, hNU, hUel, hUc, hWU⟩ := ih (Nat.card Q + Nat.card Q) (by omega) Q Q W Y
        le_rfl hQp le_rfl Subgroup.le_normalizer hWQ (hQP.trans hPW) hW hYQ hY hYc hWY
      have hWC : ∀ w ∈ W, w ∈ Q ⊓ Subgroup.centralizer (W : Set G) := fun w hw =>
        ⟨hWQ hw, Subgroup.mem_centralizer_iff.mpr (fun h hh => k3_comm hW.1 hh hw)⟩
      have hUC' : ∀ u ∈ U, u ∈ Q ⊓ Subgroup.centralizer (W : Set G) := fun u hu =>
        ⟨hUQ hu, Subgroup.mem_centralizer_iff.mpr (fun h hh => k3_comm hUel (hWU hh) hu)⟩
      have hWcent : ∀ w ∈ W, K3Cent (Q ⊓ Subgroup.centralizer (W : Set G)) w := by
        intro w hw d hd
        exact (Subgroup.mem_centralizer_iff.mp hd.2 w hw).symm
      have hUc' : Nat.card U = p * Nat.card W := by rw [hUc, hW.2]; ring
      have hUCm := k3_commutator_mem hQp hWQ hUQ hWU hNU (hQP.trans hPW) hUc' (inf_le_left :
        Q ⊓ Subgroup.centralizer (W : Set G) ≤ Q)
      set T : Subgroup G := k3T hp hp2 (Q ⊓ Subgroup.centralizer (W : Set G)) with hT
      have hWT : W ≤ T := fun w hw => by
        refine mem_k3T.mpr ⟨hWC w hw, hW.1.2 w hw, fun c hc => ?_⟩
        have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
        have e : c * w * c⁻¹ * w⁻¹ = 1 := by rw [hcw]; group
        rw [e]
        exact k3Cent_one _
      have hUT : U ≤ T := fun u hu => by
        refine mem_k3T.mpr ⟨hUC' u hu, hUel.2 u hu, fun c hc => ?_⟩
        exact hWcent _ (hUCm c hc u hu)
      have hTC : T ≤ Q ⊓ Subgroup.centralizer (W : Set G) := fun x hx => (mem_k3T.mp hx).1
      have hTP : T ≤ P := hTC.trans (inf_le_left.trans hQP)
      have hWP : W ≤ P := hWQ.trans hQP
      have hcardT : Nat.card W < Nat.card T := by
        have h1 := Subgroup.card_le_of_le hUT
        rw [hUc] at h1
        rw [hW.2]
        have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      have hWlt : W < T := lt_of_le_of_ne hWT (fun h => by
        rw [h] at hcardT; exact lt_irrefl _ hcardT)
      obtain ⟨S, hWS, hST, hPS, hScard⟩ := k3_step hP hTP hWP hWT hPW
        (k3T_normalizer (hPC := k3_normalizes_inter hPQ hPW)) hWlt
      have hSc : Nat.card S = p ^ 3 := by rw [hScard, hW.2]; ring
      have hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w := fun w hw s hs =>
        Subgroup.mem_centralizer_iff.mp (hTC (hST hs)).2 w hw
      have hScomm := k3_comm_of_index hWS hWc hScard
      have hSel : IsElemAbelian p S :=
        ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hScomm a.1 a.2 b.1 b.2)),
          fun x hx => (mem_k3T.mp (hST hx)).2.1⟩
      exact ⟨S, (hST.trans hTC).trans inf_le_left, hPS, hSel, hSc, hWS⟩
  ·
    have hQ₁lt : Q₁ < Q := lt_of_le_of_ne hQ₁Q hlt
    have hcardQ₁ : Nat.card Q₁ < Nat.card Q := Subgroup.card_lt_of_lt hQ₁lt
    obtain ⟨V, hVQ₁, hPV, hV, hVc, hWV⟩ := ih (Nat.card P + Nat.card Q₁) (by omega) P Q₁ W Y
      le_rfl hP (hQ₁Q.trans hQP) hPQ₁ (hWY.trans hYQ₁) hPW hW hYQ₁ hY hYc hWY
    exact ⟨V, hVQ₁.trans hQ₁Q, hPV, hV, hVc, hWV⟩

end K3Klem

section K3Final

variable {G : Type} [Group G] [Finite G]

theorem k3_exists_x {p : ℕ} [hp : Fact p.Prime] {R W E : Subgroup G} (hR : IsPGroup p R)
    (hWR : W ≤ R) (hNR : R ≤ Subgroup.normalizer (W : Set G)) (hW : IsPPlane p W)
    (hER : E ≤ R) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ∃ x ∈ R, x ∈ Subgroup.centralizer (W : Set G) ∧ x ^ p = 1 ∧ x ∉ W := by
  by_contra hno
  push Not at hno
  set K : Subgroup G := E ⊓ Subgroup.centralizer (W : Set G) with hK
  have hKW : K ≤ W := fun x hx => hno x (hER hx.1) hx.2 (hE.2 x hx.1)
  obtain ⟨X, hXE, hXK, hXcard⟩ := k3_exists_complement hE (inf_le_left : K ≤ E)
  have hXR : X ≤ R := hXE.trans hER
  have hXbot : X ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyX, hyC⟩
    rw [Subgroup.mem_bot]
    exact hXK y hyX ⟨hXE hyX, hyC⟩
  have hstab := ((CFSG.Goldschmidt.Sec82.plane_stability_of_le hp.out hR hWR hNR hW.2).2) X hXR hXbot
  have h1 : Nat.card X * Nat.card K = p ^ 3 := hXcard.trans hEc
  have hKge : p ^ 2 ≤ Nat.card K := by
    have h2 : p * p ^ 2 ≤ p * Nat.card K := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ = Nat.card X * Nat.card K := h1.symm
        _ ≤ p * Nat.card K := Nat.mul_le_mul_right _ hstab
    exact Nat.le_of_mul_le_mul_left h2 hp.out.pos
  have hKW' : K = W := Subgroup.eq_of_le_of_card_ge hKW (by rw [hW.2]; exact hKge)
  have hWE : W ≤ E := by rw [← hKW']; exact inf_le_left
  have hEC : E ≤ Subgroup.centralizer (W : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact k3_comm hE (hWE hw) he
  have hKE : K = E := by
    rw [hK]; exact inf_eq_left.mpr hEC
  have hcardWE : Nat.card W = Nat.card E := by rw [← hKW', hKE]
  rw [hW.2, hEc] at hcardWE
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
  omega

theorem k3_normal_E3 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) (h3 : 3 ≤ CFSG.Open.pRank p R) :
    ∃ V : Subgroup G, IsEkIn p 3 R V ∧ (V.subgroupOf R).Normal := by
  obtain ⟨E₁, hE₁R, hE₁, hE₁c⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt R
  obtain ⟨E₀, hE₀E₁, hE₀, hE₀c⟩ := input31_sub_of_card_le hE₁ le_rfl (m := 3)
    (by rw [hE₁c]; exact Nat.pow_le_pow_right hp.out.pos h3)
  have hE₀R : E₀ ≤ R := hE₀E₁.trans hE₁R
  obtain ⟨W, hWR, hW, hNR⟩ := normalPlaneLemma p hp.out hp2 G R hR (by omega)
  obtain ⟨x, hxR, hxC, hxp, hxW⟩ := k3_exists_x hR hWR hNR hW hE₀R hE₀ hE₀c
  obtain ⟨hYab, hYc⟩ := k3_sup_zpowers hW hxC hxp hxW
  have hYR : W ⊔ Subgroup.zpowers x ≤ R := sup_le hWR ((Subgroup.zpowers_le).mpr hxR)
  have hWY : W ≤ W ⊔ Subgroup.zpowers x := le_sup_left
  obtain ⟨V, hVR, hPV, hV, hVc, hWV⟩ := k3_klem hp.out hp2 (Nat.card R + Nat.card R) R R W
    (W ⊔ Subgroup.zpowers x) le_rfl hR le_rfl Subgroup.le_normalizer hWR hNR hW hYR hYab hYc hWY
  exact ⟨V, input31_isEkIn_iff.mpr ⟨hVR, hV, hVc⟩,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mpr hPV⟩

end K3Final

theorem input31_3_three : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ R : Subgroup G, IsPGroup p ↥R → 3 ≤ CFSG.Open.pRank p R →
      ∃ E : Subgroup G, IsEkIn p 3 R E ∧ (E.subgroupOf R).Normal := by
  intro G _ _ p hp hp2 R hR h3
  haveI : Fact p.Prime := ⟨hp⟩
  exact k3_normal_E3 hp2 hR h3

section Input31SixThree

variable {G : Type} [Group G] [Finite G]

theorem input31_three_connected_three
    (hI3 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
      ∀ R : Subgroup G, IsPGroup p ↥R → 3 ≤ CFSG.Open.pRank p R →
        ∃ E : Subgroup G, IsEkIn p 3 R E ∧ (E.subgroupOf R).Normal)
    (hG3 : Input31_GL3Rank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup G}
    (hR : IsPGroup p R) {A B : Subgroup G} (hA : IsEkIn p 5 R A) (hB : IsEkIn p 5 R B) :
    IsKConnectedIn p 3 R A B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : 3 ≤ CFSG.Open.pRank p R := by
    have := CFSG.SectionRank.le_pRank hp.one_lt (input31_isEkIn_iff.1 hA).1
      (input31_isEkIn_iff.1 hA).2.1 (input31_isEkIn_iff.1 hA).2.2
    omega
  obtain ⟨N, hNk, hNn⟩ := hI3 G p hp hp2 R hR h3
  obtain ⟨hNR, hNe, hNc⟩ := input31_isEkIn_iff.1 hNk
  have hNnorm : R ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).1 hNn
  have hDfor : ∀ {E : Subgroup G}, IsEkIn p 5 R E →
      ∃ D : Subgroup G, IsEkIn p 3 R D ∧ D ≤ E ∧ D ≤ Subgroup.centralizer (N : Set G) := by
    intro E hE
    obtain ⟨hER, hEe, hEk⟩ := input31_isEkIn_iff.1 hE
    have hGA := hG3 G p hp E N hEe hNe hNc (hER.trans hNnorm)
    rw [hEk] at hGA
    have h5 : p ^ 5 = p ^ 2 * p ^ 3 := by ring
    have h6 : p ^ 2 * p ^ 3 ≤
        p ^ 2 * Nat.card (E ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) := by
      rw [← h5]
      exact hGA
    have h7 : p ^ 3 ≤ Nat.card (E ⊓ Subgroup.centralizer (N : Set G) : Subgroup G) :=
      Nat.le_of_mul_le_mul_left h6 (pow_pos hp.pos 2)
    obtain ⟨D, hDF, hDe, hDc⟩ := input31_sub_of_card_le hEe (inf_le_left :
      E ⊓ Subgroup.centralizer (N : Set G) ≤ E) h7
    exact ⟨D, input31_isEkIn_iff.2 ⟨hDF.trans (inf_le_left.trans hER), hDe, hDc⟩,
      hDF.trans inf_le_left, hDF.trans inf_le_right⟩
  obtain ⟨DA, hDA, hDAA, hDAN⟩ := hDfor hA
  obtain ⟨DB, hDB, hDBB, hDBN⟩ := hDfor hB
  have hNk' : IsEkIn p 3 R N := hNk
  refine input31_kconnected_iff.2 ⟨(input31_isEkIn_iff.1 hA).1,
    (input31_isEkIn_iff.1 hA).2.1, ?_, (input31_isEkIn_iff.1 hB).1,
    (input31_isEkIn_iff.1 hB).2.1, ?_, Or.inr ⟨DA, DB, hDA, hDB,
      input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hA).2.1 hDAA, ?_, ?_⟩⟩
  · rw [(input31_isEkIn_iff.1 hA).2.2]
    exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · rw [(input31_isEkIn_iff.1 hB).2.2]
    exact Nat.pow_le_pow_right hp.pos (by norm_num)
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (input31_kconnStep_iff.2 ⟨hDA, hNk', hDAN⟩))
      (input31_kconnStep_iff.2 ⟨hNk', hDB, input31_le_centralizer_symm hDBN⟩)
  · exact (input31_le_centralizer_of_elemAbelian (input31_isEkIn_iff.1 hB).2.1 hDBB |>
      input31_le_centralizer_symm)

theorem input31_6_of_three
    (hI3 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
      ∀ R : Subgroup G, IsPGroup p ↥R → 3 ≤ CFSG.Open.pRank p R →
        ∃ E : Subgroup G, IsEkIn p 3 R E ∧ (E.subgroupOf R).Normal)
    (hG3 : Input31_GL3Rank) : Input31_6 := by
  intro G _ _ p hp hp2 R hR
  exact ⟨fun A B hA hB => input31_three_connected_three hI3 hG3 hp hp2 hR hA hB,
    fun A B hA hB => input31_two_connected hp hp2 hR hA hB⟩

end Input31SixThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
