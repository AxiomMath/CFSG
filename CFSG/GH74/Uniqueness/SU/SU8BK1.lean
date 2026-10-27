module

public import CFSG.GH74.Uniqueness.SU.SU8BLift

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG CFSG.GH74.Uniqueness.SU.SU8.Setup CFSG.GH74.Uniqueness.SU.SU8.BLift
open scoped commutatorElement

namespace BK

theorem isPGroup_two_of_normal_comm {Hb : Type*} [Group Hb] [Finite Hb] (hO : pPrimeCore 2 Hb = ⊥)
    (Z : Subgroup Hb) [Z.Normal] (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : IsPGroup 2 ↥Z := by
  classical
  let T : Subgroup Hb :=
    { carrier := {c | c ∈ Z ∧ Odd (orderOf c)}
      one_mem' := ⟨Z.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hao⟩ ⟨hb, hbo⟩
        refine ⟨Z.mul_mem ha hb, ?_⟩
        have hcomm : Commute a b := hZ a ha b hb
        have h1 : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) := hcomm.orderOf_mul_dvd_lcm
        have h2 : Nat.lcm (orderOf a) (orderOf b) ∣ orderOf a * orderOf b := Nat.lcm_dvd_mul _ _
        exact Odd.of_dvd_nat (hao.mul hbo) (h1.trans h2)
      inv_mem' := by
        rintro a ⟨ha, hao⟩
        exact ⟨Z.inv_mem ha, by rwa [orderOf_inv]⟩ }
  have hTn : T.Normal := by
    refine ⟨fun c hc h => ?_⟩
    obtain ⟨hcZ, hco⟩ := hc
    refine ⟨(inferInstance : Z.Normal).conj_mem _ hcZ h, ?_⟩
    have : orderOf (h * c * h⁻¹) = orderOf c := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective c
      simpa [MulAut.conj_apply] using this
    rwa [this]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card T) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (fun h2 => ?_)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 h2
    have h3 : orderOf (x : Hb) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have h4 := x.2.2
    rw [h3] at h4
    exact absurd h4 (Nat.not_odd_iff_even.mpr even_two)
  have hTbot : T = ⊥ := CFSG.pPrimeCore_eq_bot_iff.mp hO T hTn hcop
  intro x
  have hn : orderOf (x : Hb) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨a, b, hb, hnb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  have hbodd : Odd b := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hb)
  have hy : (x : Hb) ^ (2 ^ a) ∈ T := by
    refine ⟨Z.pow_mem x.2 _, ?_⟩
    have h1 : ((x : Hb) ^ (2 ^ a)) ^ b = 1 := by
      rw [← pow_mul, ← hnb, pow_orderOf_eq_one]
    exact Odd.of_dvd_nat hbodd (orderOf_dvd_of_pow_eq_one h1)
  rw [hTbot, Subgroup.mem_bot] at hy
  exact ⟨a, Subtype.ext (by simpa using hy)⟩

section Center

variable {Hb : Type*} [Group Hb]

@[expose] def Z0 (K : Subgroup Hb) : Subgroup Hb := (center ↥K).map K.subtype

theorem mem_Z0 {K : Subgroup Hb} {w : Hb} : w ∈ Z0 K ↔ w ∈ K ∧ ∀ k ∈ K, w * k = k * w := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.mp hc ⟨k, hk⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hw, hc⟩
    refine ⟨⟨w, hw⟩, Subgroup.mem_center_iff.mpr (fun g => ?_), rfl⟩
    exact Subtype.ext (hc g g.2).symm

theorem Z0_le (K : Subgroup Hb) : Z0 K ≤ K := fun _ h => (mem_Z0.mp h).1

instance Z0_normal (K : Subgroup Hb) [K.Normal] : (Z0 K).Normal := by
  refine ⟨fun w hw h => ?_⟩
  rw [mem_Z0] at hw ⊢
  refine ⟨(inferInstance : K.Normal).conj_mem _ hw.1 h, fun k hk => ?_⟩
  have hk' : h⁻¹ * k * h ∈ K := by
    have := (inferInstance : K.Normal).conj_mem _ hk h⁻¹
    simpa using this
  have h1 := hw.2 _ hk'
  calc (h * w * h⁻¹) * k = h * (w * (h⁻¹ * k * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * k * h) * w) * h⁻¹ := by rw [h1]
    _ = k * (h * w * h⁻¹) := by group

theorem perf_aux {K : Subgroup Hb} (hK : _root_.commutator ↥K = ⊤) {x : Hb}
    (hx : ∀ k ∈ K, ⁅x, k⁆ ∈ Z0 K) : ∀ k ∈ K, x * k = k * x := by
  have hxK : ∀ k : ↥K, ⁅x, (k : Hb)⁆ ∈ K := fun k => Z0_le K (hx k k.2)
  let φ : ↥K →* ↥K :=
    { toFun := fun k => ⟨⁅x, (k : Hb)⁆, hxK k⟩
      map_one' := by apply Subtype.ext; simp [commutatorElement_def]
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅x, (a : Hb) * b⁆ = ⁅x, (a : Hb)⁆ * ⁅x, (b : Hb)⁆
        have key : ⁅x, (a : Hb) * b⁆ =
            ⁅x, (a : Hb)⁆ * ((a : Hb) * ⁅x, (b : Hb)⁆ * (a : Hb)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [key]
        have hc := (mem_Z0.mp (hx b b.2)).2 a a.2
        congr 1
        calc (a : Hb) * ⁅x, (b : Hb)⁆ * (a : Hb)⁻¹
            = ⁅x, (b : Hb)⁆ * (a : Hb) * (a : Hb)⁻¹ := by rw [← hc]
          _ = ⁅x, (b : Hb)⁆ := by group }
  have hker : ∀ a b : ↥K, ⁅a, b⁆ ∈ φ.ker := by
    intro a b
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext ((mem_Z0.mp (hx a a.2)).2 (φ b : Hb) (φ b).2)
  have hle : _root_.commutator ↥K ≤ φ.ker := by
    rw [_root_.commutator, Subgroup.commutator_le]
    intro a _ b _
    exact hker a b
  have htop : φ.ker = ⊤ := eq_top_iff.mpr (hK ▸ hle)
  intro k hk
  have h1 : φ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _)
  have h2 : ⁅x, k⁆ = 1 := congrArg Subtype.val h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

end Center

section Quotient

variable {X : Type} [Group X] {O L A : Subgroup X} [O.Normal] [L.Normal]

abbrev Kb (O L : Subgroup X) [O.Normal] : Subgroup (X ⧸ O) := L.map (QuotientGroup.mk' O)

instance Kb_normal (O L : Subgroup X) [O.Normal] [L.Normal] : (Kb O L).Normal :=
  Subgroup.Normal.map ‹L.Normal› (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)

@[expose] def theta (O L : Subgroup X) [O.Normal] [L.Normal] : X →* ((X ⧸ O) ⧸ Z0 (Kb O L)) :=
  (QuotientGroup.mk' (Z0 (Kb O L))).comp (QuotientGroup.mk' O)

theorem theta_apply (x : X) :
    theta O L x = QuotientGroup.mk' (Z0 (Kb O L)) (QuotientGroup.mk' O x) := rfl

theorem card_inf_ker (hodd : Odd (Nat.card O)) (hexp : ∀ a ∈ A, a * a = 1)
    (hZA : ∀ c ∈ Z0 (Kb O L), c ∈ A.map (QuotientGroup.mk' O)) :
    Nat.card ↥(A ⊓ (theta O L).ker) = Nat.card ↥(Z0 (Kb O L)) := by
  have hπ1 : ∀ w : X ⧸ O, QuotientGroup.mk' (Z0 (Kb O L)) w = 1 ↔ w ∈ Z0 (Kb O L) :=
    fun w => QuotientGroup.eq_one_iff w
  apply Nat.card_congr
  refine Equiv.ofBijective (fun a => ⟨QuotientGroup.mk' O a.1, ?_⟩) ⟨?_, ?_⟩
  · have : theta O L a.1 = 1 := MonoidHom.mem_ker.mp a.2.2
    exact (hπ1 _).mp this
  · intro a b hab
    apply Subtype.ext
    exact mk_inj_of_exp_two hodd hexp a.2.1 b.2.1 (congrArg Subtype.val hab)
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha, rfl⟩ := hZA c hc
    exact ⟨⟨a, ha, MonoidHom.mem_ker.mpr ((hπ1 _).mpr hc)⟩, rfl⟩

theorem bhyp_of_K [Finite X] (hodd : Odd (Nat.card O)) (hexp : ∀ a ∈ A, a * a = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hdec0 : ∀ a ∈ A, ∃ l ∈ L, ∃ c : X, (∀ m ∈ L, ⁅c, m⁆ ∈ O) ∧ a = l * c)
    (hperf : _root_.commutator ↥(Kb O L) = ⊤)
    (hZA : ∀ c ∈ Z0 (Kb O L), c ∈ A.map (QuotientGroup.mk' O))
    (hcard : Nat.card ↥(Z0 (Kb O L)) = 2 ∨ Nat.card ↥(Z0 (Kb O L)) = 4) :
    BHyp (theta O L) O L A := by
  let q : X →* X ⧸ O := QuotientGroup.mk' O
  let π : (X ⧸ O) →* ((X ⧸ O) ⧸ Z0 (Kb O L)) := QuotientGroup.mk' (Z0 (Kb O L))
  have hKq : ∀ l ∈ L, q l ∈ Kb O L := fun l hl => ⟨l, hl, rfl⟩
  have hπ1 : ∀ w : X ⧸ O, π w = 1 ↔ w ∈ Z0 (Kb O L) := fun w => QuotientGroup.eq_one_iff w
  have hq1 : ∀ x : X, q x = 1 ↔ x ∈ O := fun x => QuotientGroup.eq_one_iff x
  have hcO : ∀ x y : X, ⁅x, y⁆ ∈ O ↔ q x * q y = q y * q x := fun x y => by
    rw [← hq1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hmk : ∀ x a : X, q a = q x → x * a⁻¹ ∈ O := by
    intro x a h
    have h1 : a⁻¹ * x ∈ O := QuotientGroup.eq.mp h
    have := (inferInstance : O.Normal).conj_mem _ h1 a
    simpa [mul_assoc] using this
  have hcen : ∀ x : X, (∀ m ∈ L, theta O L x * theta O L m = theta O L m * theta O L x) →
      ∀ k ∈ Kb O L, q x * k = k * q x := by
    intro x hx
    refine perf_aux hperf (fun k hk => ?_)
    obtain ⟨m, hm, rfl⟩ := hk
    rw [← hπ1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hx m hm
  have hcardAK := card_inf_ker hodd hexp hZA
  refine ⟨hodd, hexp, hcomm, hdec0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho
    show π (q o) = 1
    rw [(hq1 o).mpr ho, map_one]
  · intro x hx
    have hxZ : q x ∈ Z0 (Kb O L) := (hπ1 _).mp hx
    obtain ⟨l, hl, hlx⟩ := Z0_le _ hxZ
    exact ⟨l, hl, hmk x l hlx⟩
  · intro x hx m hm
    have hxZ : q x ∈ Z0 (Kb O L) := (hπ1 _).mp hx
    exact (hcO x m).mpr ((mem_Z0.mp hxZ).2 _ (hKq m hm))
  · intro x hx
    have hxZ : q x ∈ Z0 (Kb O L) := (hπ1 _).mp hx
    obtain ⟨a, ha, hax⟩ := hZA _ hxZ
    exact ⟨a, ha, hmk x a hax⟩
  · intro x hx m hm
    exact (hcO x m).mpr (hcen x hx _ (hKq m hm))
  · intro a haL ha
    show π (q a) = 1
    rw [hπ1]
    refine mem_Z0.mpr ⟨hKq a haL, fun k hk => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hk
    exact (hcO a m).mp (ha m hm)
  · intro x hx hall
    obtain ⟨l, hl, rfl⟩ := hx
    rw [theta_apply, hπ1]
    have h1 : ∀ m ∈ L, theta O L l * theta O L m = theta O L m * theta O L l :=
      fun m hm => hall _ ⟨m, hm, rfl⟩
    refine mem_Z0.mpr ⟨hKq l hl, hcen l h1⟩
  · rw [hcardAK]
    rcases hcard with h | h <;> omega
  · rw [hcardAK]
    rcases hcard with h | h <;> omega

end Quotient

end BK

end CFSG.GH74.Uniqueness.SU.SU8
