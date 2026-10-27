module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Rho
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Cz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

namespace Sec2

variable {G : Type} [Group G]

section Q8

variable [Finite G] {Q : Subgroup G} {z : G}

theorem mul_self_mem_zpowers (hQ8 : IsQ8Cube Q) (hcen : centerIn Q = zpowers z) {a : G}
    (ha : a ∈ Q) : a * a ∈ zpowers z := by
  have h := CFSG.RankThree.Literature.FSmith.sq_mem_center hQ8.1 (⟨a, ha⟩ : ↥Q)
  rw [← hcen, centerIn_eq_map]
  exact ⟨_, h, by simp [sq]⟩

theorem commutator_mem_zpowers (hQ8 : IsQ8Cube Q) (hcen : centerIn Q = zpowers z) {a b : G}
    (ha : a ∈ Q) (hb : b ∈ Q) : a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have h := CFSG.RankThree.Literature.FSmith.commutatorElement_mem_center hQ8.1
    (⟨a, ha⟩ : ↥Q) ⟨b, hb⟩
  rw [← hcen, centerIn_eq_map]
  exact ⟨_, h, by simp [commutatorElement_def]⟩

theorem comm_eq_one_iff_polarMinus (hQ8 : IsQ8Cube Q) (hcen : centerIn Q = zpowers z)
    (hz : orderOf z = 2) {ψ : G → (Fin 6 → ZMod 2)}
    (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
    (hsq : ∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b * a⁻¹ * b⁻¹ = 1 ↔ Sec2Omega.polarMinus (ψ a) (ψ b) = 0 := by
  classical
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  have hab : a * b ∈ Q := Q.mul_mem ha hb
  have hq : ∀ x ∈ Q, qMinus (ψ x) = if x * x = 1 then 0 else 1 := fun x hx => by
    split_ifs with h
    · exact (hsq x hx).mpr h
    · rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (qMinus (ψ x)) with h' | h'
      · exact absurd ((hsq x hx).mp h') h
      · exact h'
  have hpol : Sec2Omega.polarMinus (ψ a) (ψ b) =
      qMinus (ψ (a * b)) + qMinus (ψ a) + qMinus (ψ b) := by
    rw [← Sec2Omega.polar_qMinusForm, QuadraticMap.polar, Sec2Omega.qMinusForm_apply,
      Sec2Omega.qMinusForm_apply, Sec2Omega.qMinusForm_apply, hadd a ha b hb, CharTwo.sub_eq_add,
      CharTwo.sub_eq_add]
  have hprod : a * b * (a * b) = (b * a * b⁻¹ * a⁻¹) * (a * a) * (b * b) := by
    have h := congrArg Subtype.val
      (CFSG.RankThree.Literature.FSmith.mul_sq_eq hQ8.1 (⟨a, ha⟩ : ↥Q) ⟨b, hb⟩)
    simpa [sq, commutatorElement_def, mul_assoc] using h
  have hinv : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
  rw [hinv, inv_eq_one, hpol, hq _ hab, hq _ ha, hq _ hb, hprod]
  rcases eq_one_or_eq_of_mem_zpowers hz (commutator_mem_zpowers hQ8 hcen hb ha) with hc | hc <;>
  rcases eq_one_or_eq_of_mem_zpowers hz (mul_self_mem_zpowers hQ8 hcen ha) with h1 | h1 <;>
  rcases eq_one_or_eq_of_mem_zpowers hz (mul_self_mem_zpowers hQ8 hcen hb) with h2 | h2 <;>
  simp [hc, h1, h2, hz2, hz1] <;> decide

theorem exists_mem_inv_mul_mem_centralizer (hQ8 : IsQ8Cube Q) (hcen : centerIn Q = zpowers z)
    (hz : orderOf z = 2) {ψ : G → (Fin 6 → ZMod 2)}
    (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
    (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
    (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)
    (hsq : ∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) {c : G}
    (hcN : c ∈ normalizer (Q : Set G)) (hcz : c ∈ centralizer ({z} : Set G))
    (hc : ∀ a ∈ Q, c * a * c⁻¹ * a⁻¹ ∈ zpowers z) :
    ∃ q₀ ∈ Q, q₀⁻¹ * c ∈ centralizer (Q : Set G) := by
  classical
  choose s hsQ hsψ using hsurj
  have hz2 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  have hzc : c * z = z * c := mem_centralizer_singleton_iff.mp hcz
  have hzQ : ∀ w ∈ zpowers z, ∀ x ∈ Q, w * x = x * w := by
    intro w hw x hx
    rw [← hcen] at hw
    exact (mem_centralizer_iff.mp hw.2 x hx).symm
  have hzcw : ∀ w ∈ zpowers z, c * w * c⁻¹ = w := by
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact conj_zpow_eq hzc k
  set f : G → G := fun a => c * a * c⁻¹ * a⁻¹ with hf
  have hfmul : ∀ x ∈ Q, ∀ y ∈ Q, f (x * y) = f x * f y := by
    intro x hx y hy
    have hcx : c * x * c⁻¹ ∈ Q := (mem_normalizer_iff.mp hcN x).mp hx
    have h1 := hzQ _ (hc y hy) _ hcx
    simp only [hf]
    calc c * (x * y) * c⁻¹ * (x * y)⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹ * y⁻¹) * x⁻¹ := by group
      _ = (c * y * c⁻¹ * y⁻¹) * (c * x * c⁻¹) * x⁻¹ := by rw [h1]
      _ = (c * x * c⁻¹ * x⁻¹) * (c * y * c⁻¹ * y⁻¹) := by
          rw [mul_assoc]
          exact (hzQ _ (hc y hy) _ (Q.mul_mem hcx (Q.inv_mem hx))).trans (by group)
  have hfz : ∀ x ∈ Q, ∀ w ∈ zpowers z, f (w * x) = f x := by
    intro x hx w hw
    have hwQ : w ∈ Q := by
      rw [← hcen] at hw
      exact hw.1
    rw [hfmul w hwQ x hx]
    simp only [hf]
    rw [hzcw w hw, mul_inv_cancel, one_mul]
  set ind : G → ZMod 2 := fun w => if w = 1 then 0 else 1 with hind
  have hind_mul : ∀ w ∈ zpowers z, ∀ w' ∈ zpowers z, ind (w * w') = ind w + ind w' := by
    intro w hw w' hw'
    rcases eq_one_or_eq_of_mem_zpowers hz hw with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hz hw' with rfl | rfl <;>
      simp [hind, hz2, hz1, show (1 : ZMod 2) + 1 = 0 from rfl]
  have hind_inj : ∀ w ∈ zpowers z, ∀ w' ∈ zpowers z, ind w = ind w' → w = w' := by
    intro w hw w' hw' h
    rcases eq_one_or_eq_of_mem_zpowers hz hw with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hz hw' with rfl | rfl <;>
      simp_all
  have hfψ : ∀ x ∈ Q, f (s (ψ x)) = f x := by
    intro x hx
    have h1 : s (ψ x) * x⁻¹ ∈ zpowers z :=
      (psi_eq_iff hadd hker (hsQ _) hx).mp (hsψ _)
    have e : s (ψ x) = (s (ψ x) * x⁻¹) * x := by group
    rw [e, hfz x hx _ h1]
  let lam : (Fin 6 → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => ind (f (s v))
      map_zero' := by
        have h0 : s 0 ∈ zpowers z := (hker _ (hsQ 0)).mp (hsψ 0)
        have e : s 0 = s 0 * 1 := (mul_one _).symm
        show ind (f (s 0)) = 0
        rw [e, hfz 1 Q.one_mem _ h0]
        simp [hf, hind]
      map_add' := fun v w => by
        show ind (f (s (v + w))) = ind (f (s v)) + ind (f (s w))
        have h1 : ψ (s v * s w) = v + w := by rw [hadd _ (hsQ v) _ (hsQ w), hsψ, hsψ]
        rw [← h1, hfψ _ (Q.mul_mem (hsQ v) (hsQ w)), hfmul _ (hsQ v) _ (hsQ w)]
        exact hind_mul _ (hc _ (hsQ v)) _ (hc _ (hsQ w)) }
  let lam' : (Fin 6 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := AddMonoidHom.toZModLinearMap 2 lam
  set B := QuadraticMap.polarBilin Sec2Omega.qMinusForm with hB
  set u := (LinearMap.BilinForm.toDual B Sec2Omega.qMinusForm_nondegenerate).symm lam' with hu
  have hBu : ∀ v, Sec2Omega.polarMinus u v = lam v := by
    intro v
    have h1 := LinearMap.congr_fun
      ((LinearMap.BilinForm.toDual B Sec2Omega.qMinusForm_nondegenerate).apply_symm_apply lam') v
    rw [LinearMap.BilinForm.toDual_def] at h1
    change QuadraticMap.polarBilin Sec2Omega.qMinusForm u v = lam' v at h1
    rw [QuadraticMap.polarBilin_apply_apply, Sec2Omega.polar_qMinusForm] at h1
    exact h1
  refine ⟨s u, hsQ u, ?_⟩
  have key : ∀ a ∈ Q, c * a * c⁻¹ = s u * a * (s u)⁻¹ := by
    intro a ha
    have h1 : ind (f a) = Sec2Omega.polarMinus (ψ (s u)) (ψ a) := by
      rw [hsψ, hBu]
      show ind (f a) = ind (f (s (ψ a)))
      rw [hfψ a ha]
    have h2 : ind (s u * a * (s u)⁻¹ * a⁻¹) = Sec2Omega.polarMinus (ψ (s u)) (ψ a) := by
      have h3 := comm_eq_one_iff_polarMinus hQ8 hcen hz hadd hsq (hsQ u) ha
      rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
        (Sec2Omega.polarMinus (ψ (s u)) (ψ a)) with h | h
      · rw [h]
        simp [hind, h3.mpr h]
      · rw [h]
        have : s u * a * (s u)⁻¹ * a⁻¹ ≠ 1 := fun h' => by
          rw [h3.mp h'] at h
          exact zero_ne_one h
        simp [hind, this]
    have h4 := hind_inj _ (hc a ha) _ (commutator_mem_zpowers hQ8 hcen (hsQ u) ha)
      (h1.trans h2.symm)
    have h5 : c * a * c⁻¹ * a⁻¹ * a = s u * a * (s u)⁻¹ * a⁻¹ * a := by
      rw [h4]
    simpa using h5
  rw [mem_centralizer_iff]
  intro a ha
  calc a * ((s u)⁻¹ * c) = (s u)⁻¹ * (s u * a * (s u)⁻¹) * c := by group
    _ = (s u)⁻¹ * (c * a * c⁻¹) * c := by rw [key a ha]
    _ = (s u)⁻¹ * c * a := by group

end Q8

theorem le_center_of_inf_le {H : Type*} [Group H] [hnil : Group.IsNilpotent H] (N : Subgroup H)
    [N.Normal] (h : N ⊓ Subgroup.upperCentralSeries H 2 ≤ center H) : N ≤ center H := by
  let iter : ℕ → Subgroup H := fun i => (fun M : Subgroup H => ⁅M, ⊤⁆)^[i] N
  have hsucc : ∀ i, iter (i + 1) = ⁅iter i, ⊤⁆ := fun i =>
    Function.iterate_succ_apply' (fun M : Subgroup H => ⁅M, ⊤⁆) i N
  have hle : ∀ i, iter i ≤ N := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih =>
      rw [hsucc]
      exact (Subgroup.commutator_mono ih le_rfl).trans (Subgroup.commutator_le_left N ⊤)
  have hlcs : ∀ i, iter i ≤ (⊤ : Subgroup H).lowerCentralSeries i := by
    intro i
    induction i with
    | zero =>
      rw [Subgroup.lowerCentralSeries_zero]
      exact le_top
    | succ i ih =>
      rw [hsucc, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mono ih le_rfl
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have key : ∀ m i, i + m = n → iter i ≤ center H := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [add_zero] at hi
      subst hi
      exact (hlcs _).trans (by rw [hn]; exact bot_le)
    | succ m ih =>
      intro i hi
      have h1 := ih (i + 1) (by omega)
      have h2 : iter i ≤ Subgroup.upperCentralSeries H 2 := by
        intro x hx
        show x ∈ Subgroup.upperCentralSeries H (1 + 1)
        rw [Subgroup.mem_upperCentralSeries_succ_iff]
        intro y
        rw [Subgroup.upperCentralSeries_one]
        apply h1
        rw [hsucc]
        exact Subgroup.commutator_mem_commutator hx (mem_top y)
      exact fun x hx => h ⟨hle i hx, h2 hx⟩
  exact key n 0 (zero_add n)

theorem exists_zpow_mul_mem_oddCoreIn [Finite G] {X : Subgroup G} {z : G}
    (hXz : X ≤ centralizer ({z} : Set G)) (hsyl : IsSylowOf 2 (zpowers z) X) {x : G}
    (hx : x ∈ X) : ∃ k : ℤ, ∃ o ∈ AS76b.oddCoreIn X, x = z ^ k * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hcomm : ∀ c : ↥X, ∀ k : ℤ, z ^ k * (c : G) = (c : G) * z ^ k := fun c k =>
    (Commute.zpow_left (mem_centralizer_singleton_iff.mp (hXz c.2)).symm k).eq
  have hNC : normalizer ((P : Subgroup X) : Set X) ≤ centralizer ((P : Subgroup X) : Set X) := by
    intro c _
    rw [mem_centralizer_iff]
    intro p hp
    rw [hP] at hp
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (show (p : G) ∈ zpowers z from hp)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    exact hcomm c k
  obtain ⟨N, hNnorm, hcomp⟩ : ∃ N : Subgroup X, N.Normal ∧ N.IsComplement' (P : Subgroup X) :=
    ⟨_, MonoidHom.normal_ker _, MonoidHom.ker_transferSylow_isComplement' P hNC⟩
  have hNodd : Odd (Nat.card N) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro h
    exact P.not_dvd_index (by rw [hcomp.index_eq_card]; exact h)
  have hNn : X ≤ normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨n', hn', rfl⟩
      exact ⟨⟨c, hc⟩ * n' * ⟨c, hc⟩⁻¹, hNnorm.conj_mem n' hn' _, by simp⟩
    · rintro ⟨n', hn', hw⟩
      refine ⟨⟨c, hc⟩⁻¹ * n' * ⟨c, hc⟩, ?_, ?_⟩
      · have := hNnorm.conj_mem n' hn' ⟨c, hc⟩⁻¹
        rwa [inv_inv] at this
      · simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hw ⊢
        rw [hw]
        group
  have hNO : N.map X.subtype ≤ AS76b.oddCoreIn X :=
    le_oddCoreIn_of_le_normalizer (map_subtype_le N)
      (by rwa [card_map_of_injective X.subtype_injective]) hNn
  obtain ⟨⟨n, p⟩, hnp, -⟩ := hcomp.existsUnique ⟨x, hx⟩
  have hp : ((p : X) : G) ∈ zpowers z := by
    have h' : (p : X) ∈ (zpowers z).subgroupOf X := by
      rw [← hP]
      exact p.2
    exact h'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hp
  refine ⟨k, _, hNO ⟨n, n.2, rfl⟩, ?_⟩
  have h2 := congrArg Subtype.val hnp
  simp only [Subgroup.coe_mul] at h2
  rw [← h2, ← hk]
  exact (hcomm n k).symm

theorem ker_rho_eq [Finite G] {Q : Subgroup G} {z : G} (hQ8 : IsQ8Cube Q)
    (hcen : centerIn Q = zpowers z) (hz : orderOf z = 2) {ψ : G → (Fin 6 → ZMod 2)}
    (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
    (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
    (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)
    (hsq : ∀ a ∈ Q, qMinus (ψ a) = 0 ↔ a * a = 1) {K : Subgroup G}
    (hK : K ≤ normalizer (Q : Set G) ⊓ centralizer ({z} : Set G)) (hQK : Q ≤ K)
    (hsyl : IsSylowOf 2 (zpowers z) (K ⊓ centralizer (Q : Set G))) :
    (rho hadd hsurj hker hK).ker =
      (Q ⊔ AS76b.oddCoreIn (K ⊓ centralizer (Q : Set G))).subgroupOf K := by
  have hzQ : z ∈ Q := by
    have h : z ∈ centerIn Q := by rw [hcen]; exact mem_zpowers z
    exact h.1
  ext m
  constructor
  · intro hm
    rw [MonoidHom.mem_ker, rho_eq_one_iff] at hm
    rw [mem_subgroupOf]
    obtain ⟨q₀, hq₀, hc⟩ := exists_mem_inv_mul_mem_centralizer hQ8 hcen hz hadd hsurj hker hsq
      (hK m.2).1 (hK m.2).2 hm
    have hcK : q₀⁻¹ * m ∈ K ⊓ centralizer (Q : Set G) :=
      mem_inf.mpr ⟨mul_mem (inv_mem (hQK hq₀)) m.2, hc⟩
    have hXz : K ⊓ centralizer (Q : Set G) ≤ centralizer ({z} : Set G) :=
      fun x hx => (hK hx.1).2
    obtain ⟨k, o, ho, hko⟩ := exists_zpow_mul_mem_oddCoreIn hXz hsyl hcK
    have e : (m : G) = (q₀ * z ^ k) * o := by
      rw [mul_assoc, ← hko]
      group
    rw [e]
    exact mul_mem (mem_sup_left (mul_mem hq₀ (zpow_mem hzQ k))) (mem_sup_right ho)
  · intro hm
    rw [mem_subgroupOf] at hm
    have hY : Q ⊔ AS76b.oddCoreIn (K ⊓ centralizer (Q : Set G)) ≤
        (rho hadd hsurj hker hK).ker.map K.subtype := by
      refine sup_le (fun q hq => ⟨⟨q, hQK hq⟩, MonoidHom.mem_ker.mpr
        ((rho_eq_one_iff hadd hsurj hker hK _).mpr fun a ha =>
          commutator_mem_zpowers hQ8 hcen hq ha), rfl⟩)
        (fun o ho => ⟨⟨o, (AS76b.oddCoreIn_le _ ho).1⟩, MonoidHom.mem_ker.mpr
          ((rho_eq_one_iff hadd hsurj hker hK _).mpr fun a ha => ?_), rfl⟩)
      have hoC := (AS76b.oddCoreIn_le _ ho).2
      have e : o * a * o⁻¹ * a⁻¹ = 1 := by
        rw [← mem_centralizer_iff.mp hoC a ha, mul_inv_cancel_right, mul_inv_cancel]
      exact e ▸ one_mem _
    obtain ⟨m', hm', hmm'⟩ := hY hm
    have : m' = m := Subtype.ext hmm'
    rwa [← this]

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem sylow_zpowers_centralizer_of (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) (hZQ : sec2Z A E F ≤ Q) :
    IsSylowOf 2 (zpowers z) (centralizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hQ.data.setting
  obtain ⟨-, hZS, hSS, -⟩ := h24 G A R g E F hS
  obtain ⟨-, -, -, -, -, hSsyl, -, -, -⟩ := h26 G A R g E F hS
  obtain ⟨-, hPST, -, hZ2, -, -⟩ := (h212 G A R g E F hS).2 T₀ hQ.data.le hQ.data.sylow
  have hT₀N : T₀ ≤ normalizer (Q : Set G) := hQ.T₀_le_normalizer_Q h26 h212
  have hT₀T : T₀ ≤ normalizer (sec2T E T₀ : Set G) := hQ.T₀_le_normalizer_T h212
  have hT₀2 := hQ.isPGroup_T₀
  have hT2 : IsPGroup 2 (sec2T E T₀) := hT₀2.to_le hQ.T_le_T₀
  have hST : sec2S A R E F ≤ sec2T E T₀ := le_sup_right.trans hPST
  have hST₀ : sec2S A R E F ≤ T₀ := hST.trans hQ.T_le_T₀
  have hzZ := hQ.z_mem_Z h212
  have hDT : T₀ ⊓ centralizer (Q : Set G) ⊓ sec2T E T₀ ≤ zpowers z := by
    have : Group.IsNilpotent ↥(sec2T E T₀) := hT2.isNilpotent
    have hN' : ((T₀ ⊓ centralizer (Q : Set G) ⊓ sec2T E T₀).subgroupOf (sec2T E T₀)).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun t ht =>
        Sec2.mem_normalizer_inf (Sec2.mem_normalizer_inf (le_normalizer (hQ.T_le_T₀ ht))
          (Sec2.normalizer_le_normalizer_centralizer Q (hT₀N (hQ.T_le_T₀ ht)))) (le_normalizer ht)
    have h1 := Sec2.le_center_of_inf_le
      ((T₀ ⊓ centralizer (Q : Set G) ⊓ sec2T E T₀).subgroupOf (sec2T E T₀)) (by
        rintro x ⟨hx1, hx2⟩
        have hxZ : (x : G) ∈ sec2Z A E F := by
          rw [← hZ2]
          exact ⟨x, hx2, rfl⟩
        have hxz : (x : G) ∈ zpowers z := by
          rw [← hQ.centerIn_Q]
          exact ⟨hZQ hxZ, hx1.1.2⟩
        rw [← hQ.center, Sec2.centerIn_eq_map] at hxz
        obtain ⟨w, hw, hwx⟩ := hxz
        have : w = x := Subtype.ext hwx
        rwa [← this])
    intro d hd
    have := h1 (show (⟨d, hd.2⟩ : ↥(sec2T E T₀)) ∈
      (T₀ ⊓ centralizer (Q : Set G) ⊓ sec2T E T₀).subgroupOf (sec2T E T₀) from hd)
    rw [← hQ.center, Sec2.centerIn_eq_map]
    exact ⟨_, this, rfl⟩
  have hD : T₀ ⊓ centralizer (Q : Set G) ≤
      centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F) (sec2Z A E F) := by
    rintro d ⟨hdT, hdC⟩
    have hdN : d ∈ normalizer (sec2S A R E F : Set G) := hQ.data.sylow.le hdT
    refine ⟨hdN, hZS ▸ Sec2.mem_normalizer_centerIn hdN, fun s hs => ?_⟩
    have hsT₀ : s ∈ T₀ := hST₀ hs
    have h1 : s⁻¹ * d⁻¹ * s * d ∈ T₀ ⊓ centralizer (Q : Set G) ⊓ sec2T E T₀ := by
      refine mem_inf.mpr ⟨mem_inf.mpr
        ⟨mul_mem (mul_mem (mul_mem (inv_mem hsT₀) (inv_mem hdT)) hsT₀) hdT, ?_⟩, ?_⟩
      · have := (mem_normalizer_iff.mp (Sec2.normalizer_le_normalizer_centralizer Q
          (inv_mem (hT₀N hsT₀))) d⁻¹).mp (inv_mem hdC)
        rw [inv_inv] at this
        exact mul_mem this hdC
      · have := (mem_normalizer_iff.mp (hT₀T (inv_mem hdT)) s).mp (hST hs)
        rw [inv_inv] at this
        have e : s⁻¹ * d⁻¹ * s * d = s⁻¹ * (d⁻¹ * s * d) := by group
        rw [e]
        exact mul_mem (inv_mem (hST hs)) this
    exact (zpowers_le.mpr hzZ) (hDT h1)
  have hScm : sec2S A R E F ≤ centralizerMod (normalizer (sec2S A R E F : Set G))
      (sec2S A R E F) (sec2Z A E F) := by
    intro s hs
    refine ⟨le_normalizer hs, hZS ▸ Sec2.mem_normalizer_centerIn (le_normalizer hs),
      fun w hw => ?_⟩
    rw [← hSS]
    have := Subgroup.commutator_mem_commutator (inv_mem hw) (inv_mem hs)
    simpa [commutatorElement_def] using this
  have hDS : T₀ ⊓ centralizer (Q : Set G) ≤ sec2S A R E F := by
    have heq := hSsyl.eq_of_le
      (le_sup_left : sec2S A R E F ≤ sec2S A R E F ⊔ (T₀ ⊓ centralizer (Q : Set G)))
      (sup_le hScm hD) (hT₀2.to_le (sup_le hST₀ inf_le_left))
    rw [← heq]
    exact le_sup_right
  have hDz : T₀ ⊓ centralizer (Q : Set G) = zpowers z := by
    refine le_antisymm (fun d hd => hDT ⟨hd, hST (hDS hd)⟩) ?_
    rw [zpowers_le]
    exact ⟨hQ.T_le_T₀ hQ.z_mem_T, hQ.z_mem_centralizer_Q⟩
  have hzQ : {z} ⊆ (Q : Set G) := Set.singleton_subset_iff.mpr hQ.z_mem_Q
  have hCz : centralizer (Q : Set G) ≤ centralizer ({z} : Set G) := Subgroup.centralizer_le hzQ
  have hCN : centralizer (Q : Set G) ≤ normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have h1 : IsSylowOf 2 T₀ (centralizer ({z} : Set G) ⊓ normalizer (Q : Set G)) :=
    (hQ.sylow_T₀_centralizer h212).of_le (le_inf (hQ.T₀_le_centralizer h212) hT₀N) inf_le_left
  have h2 := h1.inf_of_le_normalizer (le_inf hCz hCN)
    (inf_le_right.trans (Sec2.normalizer_le_normalizer_centralizer Q))
  rwa [hDz] at h2

end Sec2Q

end CFSG.ComponentClassification.AS81
