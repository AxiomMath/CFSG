module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour

open CFSG.LieType.Steinberg
open scoped commutatorElement

section Central

variable {X : Type*} [Group X]

@[expose] def CentralIn (Z K : Subgroup X) : Prop :=
  Z ≤ K ∧ ∀ z ∈ Z, ∀ κ ∈ K, z * κ = κ * z

theorem conj_eq_of_comm_mem {K Z : Subgroup X} [K.Normal] (hK : commutator K = ⊤)
    (hZ : CentralIn Z K) {x : X} (hx : ∀ κ ∈ K, x * κ * x⁻¹ * κ⁻¹ ∈ Z) :
    ∀ κ ∈ K, x * κ * x⁻¹ = κ := by
  have hmem : ∀ κ : K, x * (κ : X) * x⁻¹ * (κ : X)⁻¹ ∈ K := fun κ =>
    K.mul_mem (‹K.Normal›.conj_mem _ κ.2 x) (K.inv_mem κ.2)
  have hc : ∀ κ : K, (⟨x * (κ : X) * x⁻¹ * (κ : X)⁻¹, hmem κ⟩ : K) ∈ Subgroup.center K := by
    intro κ
    rw [Subgroup.mem_center_iff]
    intro κ'
    exact Subtype.ext (hZ.2 _ (hx κ κ.2) κ' κ'.2).symm
  let φ : K →* Subgroup.center K :=
    { toFun := fun κ => ⟨⟨x * (κ : X) * x⁻¹ * (κ : X)⁻¹, hmem κ⟩, hc κ⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro κ κ'
        apply Subtype.ext
        apply Subtype.ext
        have h1 : x * (κ' : X) * x⁻¹ * (κ' : X)⁻¹ * (κ : X)⁻¹ =
            (κ : X)⁻¹ * (x * (κ' : X) * x⁻¹ * (κ' : X)⁻¹) :=
          hZ.2 _ (hx κ' κ'.2) _ (K.inv_mem κ.2)
        calc x * ((κ : X) * (κ' : X)) * x⁻¹ * ((κ : X) * (κ' : X))⁻¹
            = (x * (κ : X) * x⁻¹) * (x * (κ' : X) * x⁻¹ * (κ' : X)⁻¹) * (κ : X)⁻¹ := by group
          _ = (x * (κ : X) * x⁻¹) * ((κ : X)⁻¹ * (x * (κ' : X) * x⁻¹ * (κ' : X)⁻¹)) := by
            rw [mul_assoc _ _ ((κ : X)⁻¹), h1]
          _ = (x * (κ : X) * x⁻¹ * (κ : X)⁻¹) * (x * (κ' : X) * x⁻¹ * (κ' : X)⁻¹) := by group }
  have hker : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  intro κ hκ
  have hk : (⟨κ, hκ⟩ : K) ∈ commutator K := by rw [hK]; exact Subgroup.mem_top _
  have h := congrArg (fun y : Subgroup.center K => ((y : K) : X)) (MonoidHom.mem_ker.1 (hker hk))
  have h' : x * κ * x⁻¹ * κ⁻¹ = 1 := h
  exact mul_inv_eq_one.1 h'

theorem eq_top_of_perfect_of_dec {G : Type*} [Group G] (hG : commutator G = ⊤) {L : Subgroup G}
    (hdec : ∀ g : G, ∃ z ∈ Subgroup.center G, ∃ l ∈ L, g = z * l) : L = ⊤ := by
  have hcomm : commutator G ≤ L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨z, hz, l, hl, rfl⟩ := hdec a
    obtain ⟨z', hz', l', hl', rfl⟩ := hdec b
    rw [commutatorElement_mul_mul_of_mem_center hz hz']
    simp only [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) (L.inv_mem hl')
  rw [hG] at hcomm
  exact eq_top_iff.2 hcomm

theorem le_of_perfect_of_dec {K L Z : Subgroup X} (hK : commutator K = ⊤) (hLK : L ≤ K)
    (hZ : CentralIn Z K) (hdec : ∀ k ∈ K, ∃ z ∈ Z, ∃ l ∈ L, k = z * l) : K ≤ L := by
  have key := eq_top_of_perfect_of_dec (G := K) hK (L := L.subgroupOf K) fun g => by
    obtain ⟨z, hz, l, hl, hg⟩ := hdec g g.2
    refine ⟨⟨z, hZ.1 hz⟩, ?_, ⟨l, hLK hl⟩, hl, Subtype.ext hg⟩
    rw [Subgroup.mem_center_iff]
    intro κ
    exact Subtype.ext (hZ.2 z hz κ κ.2).symm
  intro k hk
  have : (⟨k, hk⟩ : K) ∈ L.subgroupOf K := by rw [key]; exact Subgroup.mem_top _
  exact this

theorem mem_center_subtype_iff {K : Subgroup X} (κ : K) :
    κ ∈ Subgroup.center K ↔ ∀ κ' ∈ K, (κ : X) * κ' = κ' * κ := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h κ' hκ'
    exact (congrArg Subtype.val (h ⟨κ', hκ'⟩)).symm
  · intro h g
    exact Subtype.ext (h g g.2).symm

end Central

section TwoPart

variable {X : Type*} [Group X]

@[expose] def twoPart (K : Subgroup X) : Subgroup X where
  carrier := {y | y ∈ K ∧ (∀ k ∈ K, y * k = k * y) ∧ ∃ n : ℕ, y ^ 2 ^ n = 1}
  mul_mem' := by
    rintro a b ⟨haK, hac, n, hn⟩ ⟨hbK, hbc, m, hm⟩
    refine ⟨K.mul_mem haK hbK, fun k hk => ?_, n + m, ?_⟩
    · rw [mul_assoc, hbc k hk, ← mul_assoc, hac k hk, mul_assoc]
    · have hab : Commute a b := hac b hbK
      rw [hab.mul_pow, pow_add, pow_mul, pow_mul', hn, hm, one_pow, one_pow, one_mul]
  one_mem' := ⟨K.one_mem, fun k _ => by simp, 0, by simp⟩
  inv_mem' := by
    rintro a ⟨haK, hac, n, hn⟩
    exact ⟨K.inv_mem haK, fun k hk => (Commute.inv_left (hac k hk) : Commute a⁻¹ k).eq, n,
      by rw [inv_pow, hn, inv_one]⟩

theorem centralIn_twoPart (K : Subgroup X) : CentralIn (twoPart K) K :=
  ⟨fun _ h => h.1, fun _ hz κ hκ => hz.2.1 κ hκ⟩

instance normal_twoPart (K : Subgroup X) [K.Normal] : (twoPart K).Normal where
  conj_mem := by
    rintro y ⟨hyK, hyc, n, hn⟩ g
    refine ⟨‹K.Normal›.conj_mem y hyK g, fun k hk => ?_, n, ?_⟩
    · have hk' : g⁻¹ * k * g ∈ K := by simpa using ‹K.Normal›.conj_mem k hk g⁻¹
      have h := hyc _ hk'
      calc g * y * g⁻¹ * k = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by rw [h]
        _ = k * (g * y * g⁻¹) := by group
    · rw [conj_pow, hn, mul_one, mul_inv_cancel]

theorem isPGroup_twoPart (K : Subgroup X) : IsPGroup 2 (twoPart K) := by
  rintro ⟨y, _, _, n, hn⟩
  exact ⟨n, Subtype.ext hn⟩

theorem mem_twoPart_of_sq_mem {K : Subgroup X} {y : X} (hyK : y ∈ K)
    (hyc : ∀ k ∈ K, y * k = k * y) (h : y ^ 2 ∈ twoPart K) : y ∈ twoPart K := by
  obtain ⟨-, -, n, hn⟩ := h
  exact ⟨hyK, hyc, n + 1, by rw [pow_succ', pow_mul, hn]⟩

end TwoPart

section Image

variable {X X' : Type*} [Group X] [Group X'] {K : Subgroup X} [K.Normal]

theorem mem_center_map_iff (hK : commutator K = ⊤) {π : X →* X'} (hπ : π.ker = twoPart K)
    {x : X} (hx : x ∈ K) :
    (⟨π x, Subgroup.mem_map_of_mem π hx⟩ : K.map π) ∈ Subgroup.center (K.map π) ↔
      ∀ κ ∈ K, x * κ = κ * x := by
  constructor
  · intro h
    have hall : ∀ κ ∈ K, x * κ * x⁻¹ * κ⁻¹ ∈ twoPart K := by
      intro κ hκ
      have h1 := Subgroup.mem_center_iff.1 h ⟨π κ, Subgroup.mem_map_of_mem π hκ⟩
      have h3 : π κ * π x = π x * π κ := congrArg Subtype.val h1
      rw [← hπ, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_one, ← h3, mul_inv_cancel_right]
    intro κ hκ
    have h4 := conj_eq_of_comm_mem hK (centralIn_twoPart K) hall κ hκ
    calc x * κ = (x * κ * x⁻¹) * x := by group
      _ = κ * x := by rw [h4]
  · intro h
    rw [Subgroup.mem_center_iff]
    rintro ⟨y, κ, hκ, rfl⟩
    apply Subtype.ext
    change π κ * π x = π x * π κ
    rw [← map_mul, ← map_mul, h κ hκ]

theorem odd_card_center_map (hK : commutator K = ⊤) {π : X →* X'} (hπ : π.ker = twoPart K)
    [Finite (K.map π)] : Odd (Nat.card (Subgroup.center (K.map π))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center (K.map π)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center (K.map π))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨x, hxK, hxy⟩ := Subgroup.mem_map.1 (y : Subgroup.center (K.map π)).1.2
  have hxc : ∀ κ ∈ K, x * κ = κ * x := by
    refine (mem_center_map_iff hK hπ hxK).1 ?_
    have : (⟨π x, Subgroup.mem_map_of_mem π hxK⟩ : K.map π) = (y : K.map π) :=
      Subtype.ext hxy
    rw [this]
    exact y.2
  have hx2 : x ^ 2 ∈ twoPart K := by
    rw [← hπ, MonoidHom.mem_ker, map_pow, hxy]
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg (fun z : Subgroup.center (K.map π) => ((z : K.map π) : X')) this
  have hx : x ∈ twoPart K := mem_twoPart_of_sq_mem hxK hxc hx2
  have hπx : π x = 1 := by rw [← MonoidHom.mem_ker, hπ]; exact hx
  have hy1 : y = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hxy.symm.trans hπx
  rw [hy1, orderOf_one] at hy
  omega

end Image

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour
