module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex
import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniChief
import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniFaithful

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSJ2

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf_of_normal {K : Type} [Group K] (A B : Subgroup K) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup K) * Nat.card (A ⊓ B : Subgroup K) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf [Finite G] {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

theorem relIndex_mul_card_of_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have := Subgroup.relIndex_mul_card (H := H) (K := K)
  rwa [inf_eq_left.mpr h] at this

theorem comm_mul_left (a b g : G) : ⁅a * b, g⁆ = (a * ⁅b, g⁆ * a⁻¹) * ⁅a, g⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right (a b g : G) : ⁅a, b * g⁆ = ⁅a, b⁆ * (b * ⁅a, g⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem conj_mem_of_mem_normalizer' {Q : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) : g * x * g⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem le_normalizer_frat [Finite G] {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((dsFrattini Q : Subgroup G) : Set G) :=
  frattiniChief_mem_normalizer Q hg

theorem comm_mem_frat [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) {q e : G}
    (hq : q ∈ Q) (he : e ∈ Q) : ⁅q, e⁆ ∈ dsFrattini Q :=
  frattiniChief_comm_mem Q hQ hq he

theorem mem_of_index_two {H K : Subgroup G} (h : H.relIndex K = 2) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  obtain ⟨a, _, ha⟩ := Subgroup.relIndex_eq_two_iff'.mp h
  have h1 : a * x ∈ H := by
    rcases ha x hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hxH
  have h2 : a * y ∈ H := by
    rcases ha y hy with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hyH
  have e : x⁻¹ * y = (a * x)⁻¹ * (a * y) := by group
  rw [e]
  exact H.mul_mem (H.inv_mem h1) h2

theorem comm_mem_of_index_two {Z Z2 : Subgroup G} {t : G}
    (hrel : Z.relIndex Z2 = 2) (htZ2 : t ∈ Subgroup.normalizer (Z2 : Set G))
    (htZ : ∀ z ∈ Z, t * z = z * t) {e : G} (he : e ∈ Z2) :
    ⁅e, t⁆ ∈ Z := by
  rw [commutatorElement_def]
  by_cases heZ : e ∈ Z
  · have h1 : t * e = e * t := htZ e heZ
    have h2 : e * t * e⁻¹ * t⁻¹ = 1 := by
      calc e * t * e⁻¹ * t⁻¹ = (t * e) * e⁻¹ * t⁻¹ := by rw [← h1]
        _ = 1 := by group
    rw [h2]
    exact Z.one_mem
  · have he'Z2 : t * e * t⁻¹ ∈ Z2 := conj_mem_of_mem_normalizer' htZ2 he
    have he'Z : t * e * t⁻¹ ∉ Z := by
      intro h
      apply heZ
      have h6 : t * (t * e * t⁻¹) = (t * e * t⁻¹) * t := htZ _ h
      have hX : e = t * e * t⁻¹ := by
        calc e = t⁻¹ * (t * e * t⁻¹) * t := by group
          _ = t⁻¹ * ((t * e * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * e * t⁻¹)) := by rw [h6]
          _ = t * e * t⁻¹ := by group
      rw [hX]
      exact h
    have e2 : e * t * e⁻¹ * t⁻¹ = e * (t * e * t⁻¹)⁻¹ := by group
    rw [e2]
    have := mem_of_index_two hrel (x := e⁻¹) (y := (t * e * t⁻¹)⁻¹) (Z2.inv_mem he)
      (Z2.inv_mem he'Z2) (fun h => heZ (by simpa using Z.inv_mem h))
      (fun h => he'Z (by simpa using Z.inv_mem h))
    simpa using this

theorem mem_of_comm_mem_frat [Finite G] {Q W' W'' : Subgroup G} {d : G}
    (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    (hW'N : Q ≤ Subgroup.normalizer (W' : Set G))
    (hsup : W' ⊔ W'' = Q) (hΦW'' : dsFrattini Q ≤ W'')
    (hfix : FixFree (dsFrattini Q) W' d) (hd : ∀ w ∈ W'', ⁅d, w⁆ ∈ dsFrattini Q)
    {z : G} (hz : z ∈ Q) (hzd : ⁅z, d⁆ ∈ dsFrattini Q) : z ∈ W'' := by
  have hW''Q : W'' ≤ Q := le_sup_right.trans hsup.le
  have hW'Q : W' ≤ Q := le_sup_left.trans hsup.le
  have hW''N : W'' ≤ Subgroup.normalizer (W' : Set G) := fun w hw => hW'N (hW''Q hw)
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hW''N).1
    (by rw [hsup]; exact hz)
  have hbd : ⁅b, d⁆ ∈ dsFrattini Q := by
    rw [← commutatorElement_inv]
    exact (dsFrattini Q).inv_mem (hd b hb)
  have ha_N : a ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer (hW'Q ha)
  have hcon : a * ⁅b, d⁆ * a⁻¹ ∈ dsFrattini Q := frattiniChief_conj_mem Q ha_N hbd
  have hx := comm_mul_left a b d
  have hcd : ⁅a, d⁆ ∈ dsFrattini Q := by
    have e : ⁅a, d⁆ = (a * ⁅b, d⁆ * a⁻¹)⁻¹ * ⁅a * b, d⁆ := by
      rw [hx]
      group
    rw [e]
    exact (dsFrattini Q).mul_mem ((dsFrattini Q).inv_mem hcon) hzd
  have ha' : a ∈ dsFrattini Q := hfix a ha hcd
  exact W''.mul_mem (hΦW'' ha') hb

theorem fix_dichotomy [Finite G] {Z2 Φ : Subgroup G} {k : G}
    (hkZ : k ∈ Subgroup.normalizer (Z2 : Set G)) (hkΦ : k ∈ Subgroup.normalizer (Φ : Set G))
    (hfix : FixFree ⊥ Z2 k) (hZ2 : Nat.card Z2 = 4) :
    Z2 ⊓ Φ = ⊥ ∨ Z2 ≤ Φ := by
  have hdvd : Nat.card ↥(Z2 ⊓ Φ) ∣ 4 := hZ2 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hpow : Nat.card ↥(Z2 ⊓ Φ) ∣ 2 ^ 2 := by simpa using hdvd
  obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpow
  interval_cases i
  · left
    rw [← Subgroup.card_eq_one]
    simpa using hcard
  · exfalso
    have hcard2 : Nat.card ↥(Z2 ⊓ Φ) = 2 := by simpa using hcard
    obtain ⟨c, hc1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Z2 ⊓ Φ))).1 hcard2
    have hcH : (c : G) ∈ Z2 ⊓ Φ := c.2
    have hcZ : (c : G) ∈ Z2 := (inf_le_left : Z2 ⊓ Φ ≤ Z2) hcH
    have hcΦ : (c : G) ∈ Φ := (inf_le_right : Z2 ⊓ Φ ≤ Φ) hcH
    have hcne : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hconj : k⁻¹ * (c : G) * k ∈ Z2 ⊓ Φ := by
      constructor
      · have := conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ hkZ) hcZ
        simpa using this
      · have := conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ hkΦ) hcΦ
        simpa using this
    have hyne : (⟨k⁻¹ * (c : G) * k, hconj⟩ : ↥(Z2 ⊓ Φ)) ≠ 1 := by
      intro h
      have h' : k⁻¹ * (c : G) * k = 1 := congrArg Subtype.val h
      apply hcne
      calc (c : G) = k * (k⁻¹ * (c : G) * k) * k⁻¹ := by group
        _ = 1 := by rw [h']; group
    have hconj' := huniq _ hyne
    have hc_eq : k⁻¹ * (c : G) * k = c := congrArg Subtype.val hconj'
    have hck : (c : G) * k = k * c := by
      calc (c : G) * k = k * (k⁻¹ * (c : G) * k) := by group
        _ = k * c := by rw [hc_eq]
    have hcomm : ⁅(c : G), k⁆ = 1 := by
      rw [commutatorElement_def, hck]
      group
    have hmem : (c : G) ∈ (⊥ : Subgroup G) :=
      hfix (c : G) hcZ (Subgroup.mem_bot.mpr hcomm)
    exact hcne (Subgroup.mem_bot.mp hmem)
  · right
    have hH : Z2 ⊓ Φ = Z2 := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hZ2, hcard]
      norm_num
    exact (le_of_eq hH.symm).trans inf_le_right

theorem exists_central_involution [Finite G] {W : Subgroup G} (hW : Nat.card W = 16) :
    ∃ u ∈ W, u ≠ 1 ∧ u ^ 2 = 1 ∧ ∀ w ∈ W, u * w = w * u := by
  have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 4) (by rw [hW]; norm_num)
  haveI : Nontrivial ↥W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hW]
    norm_num
  have hC : Nat.card ↥(Subgroup.center ↥W) ∣ 2 ^ 4 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥W)
    rwa [hW] at this
  haveI : Nontrivial ↥(Subgroup.center ↥W) := (IsPGroup.center_nontrivial hW2)
  have hC2 : IsPGroup 2 ↥(Subgroup.center ↥W) := IsPGroup.of_card_dvd_pow hC
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hC2).mp inferInstance
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥W) := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥W)) 2 h2
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    norm_num at hx
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  refine ⟨((x : ↥W) : G), (x : ↥W).2, ?_, ?_, ?_⟩
  · intro h
    apply hx1
    exact Subtype.ext (Subtype.ext h)
  · have h := congrArg (fun y : ↥(Subgroup.center ↥W) => ((y : ↥W) : G)) hx2
    simpa using h
  · intro w hw
    have hc := Subgroup.mem_center_iff.mp x.2 ⟨w, hw⟩
    have h := congrArg (fun y : ↥W => (y : G)) hc
    simpa using h.symm

theorem caseA_false [Finite G] {Q W' W'' Z2 : Subgroup G} {d : G}
    (hQ : IsPGroup 2 Q) (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    (hZ2Q : Z2 ≤ Q) (hZ2c : ∀ z ∈ Z2, ∀ q ∈ Q, q * z = z * q)
    (hZ2d : ∀ z ∈ Z2, ⁅d, z⁆ = 1) (hZ2card : Nat.card Z2 = 4)
    (hZ2Ω : Z2 = dsOmega1 (centerOf Q))
    (hQcard : Nat.card Q = 64) (hΦcard : Nat.card (dsFrattini Q) = 4)
    (hW'N : Q ≤ Subgroup.normalizer (W' : Set G)) (hsup : W' ⊔ W'' = Q)
    (hΦW' : dsFrattini Q ≤ W') (hΦW'' : dsFrattini Q ≤ W'')
    (hrelW' : (dsFrattini Q).relIndex W' = 4) (hrelW'' : (dsFrattini Q).relIndex W'' = 4)
    (hfix : FixFree (dsFrattini Q) W' d) (hdW'' : ∀ w ∈ W'', ⁅d, w⁆ ∈ dsFrattini Q)
    (hcase : Z2 ⊓ dsFrattini Q = ⊥) : False := by
  have hW'Q : W' ≤ Q := le_sup_left.trans hsup.le
  have hZ2N : Z2 ≤ Subgroup.normalizer ((dsFrattini Q : Subgroup G) : Set G) :=
    fun z hz => le_normalizer_frat (Subgroup.le_normalizer (hZ2Q hz))
  have hZ2N' : Z2 ≤ Subgroup.normalizer (W' : Set G) := fun z hz => hW'N (hZ2Q hz)
  have hA1 : ∀ z ∈ Q, ⁅z, d⁆ ∈ dsFrattini Q → z ∈ W'' := fun z hz hzd =>
    mem_of_comm_mem_frat hdQ hW'N hsup hΦW'' hfix hdW'' hz hzd
  have hZ2W'' : Z2 ≤ W'' := fun z hz => hA1 z (hZ2Q hz) (by
    rw [← commutatorElement_inv, hZ2d z hz, inv_one]
    exact (dsFrattini Q).one_mem)
  have hW''card : Nat.card W'' = 16 := by
    have := relIndex_mul_card_of_le hΦW''
    rw [hrelW'', hΦcard] at this
    omega
  have hW'card : Nat.card W' = 16 := by
    have := relIndex_mul_card_of_le hΦW'
    rw [hrelW', hΦcard] at this
    omega
  have hΦW''eq : dsFrattini Q ⊔ Z2 = W'' := by
    have h := card_sup_mul_card_inf hZ2N
    have hinf : dsFrattini Q ⊓ Z2 = ⊥ := by rw [inf_comm]; exact hcase
    rw [hinf, Subgroup.card_bot, hΦcard, hZ2card] at h
    apply Subgroup.eq_of_le_of_card_ge (sup_le hΦW'' hZ2W'')
    rw [hW''card]
    omega
  have hW'Z2 : W' ⊔ Z2 = Q := by
    apply le_antisymm (sup_le hW'Q hZ2Q)
    rw [← hsup, ← hΦW''eq]
    exact sup_le le_sup_left (sup_le (hΦW'.trans le_sup_left) le_sup_right)
  have hW'Z2inf : W' ⊓ Z2 = ⊥ := by
    have h := card_sup_mul_card_inf hZ2N'
    rw [hW'Z2, hQcard, hW'card, hZ2card] at h
    rw [← Subgroup.card_eq_one]
    omega
  obtain ⟨u, huW', hu1, hu2, hucomm⟩ := exists_central_involution hW'card
  have huQ : u ∈ Q := hW'Q huW'
  have hucQ : ∀ q ∈ Q, u * q = q * u := by
    intro q hq
    have hq' : q ∈ W' ⊔ Z2 := by rw [hW'Z2]; exact hq
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hZ2N').1 hq'
    calc u * (a * b) = (u * a) * b := by group
      _ = (a * u) * b := by rw [hucomm a ha]
      _ = a * (u * b) := by group
      _ = a * (b * u) := by rw [hZ2c b hb u huQ]
      _ = (a * b) * u := by group
  have hu_cent : u ∈ centerOf Q :=
    ⟨huQ, Subgroup.mem_centralizer_iff.mpr (fun g hg => (hucQ g hg).symm)⟩
  have huZ2 : u ∈ Z2 := by
    rw [hZ2Ω]
    exact Subgroup.subset_closure ⟨hu_cent, hu2⟩
  have hmem : u ∈ W' ⊓ Z2 := ⟨huW', huZ2⟩
  rw [hW'Z2inf] at hmem
  exact hu1 (Subgroup.mem_bot.mp hmem)

theorem caseB_false [Finite G] {Q W' W'' : Subgroup G} {t t' : G}
    (hQ : IsPGroup 2 Q) (ht : t ∈ Subgroup.normalizer (Q : Set G))
    (htQ : t ∉ Q) (hcos : t⁻¹ * t' ∈ Q)
    (hsup : W' ⊔ W'' = Q) (hW'N : Q ≤ Subgroup.normalizer (W' : Set G))
    (hW'_t : ∀ w ∈ W', ⁅w, t⁆ ∈ dsFrattini Q)
    (hW''_t' : ∀ w ∈ W'', ⁅w, t'⁆ ∈ dsFrattini Q)
    (hburn : (∀ q ∈ Q, ⁅t, q⁆ ∈ dsFrattini Q) → t ∈ Q) : False := by
  have hW'Q : W' ≤ Q := le_sup_left.trans hsup.le
  have hW''Q : W'' ≤ Q := le_sup_right.trans hsup.le
  have hW''N : W'' ≤ Subgroup.normalizer (W' : Set G) := fun w hw => hW'N (hW''Q hw)
  have hB5 : ∀ w ∈ W'', ⁅w, t⁆ ∈ dsFrattini Q := by
    intro w hw
    have hwQ : w ∈ Q := hW''Q hw
    have ht'eq : t' = t * (t⁻¹ * t') := by group
    have hkey : ⁅w, t'⁆ = ⁅w, t⁆ * (t * ⁅w, t⁻¹ * t'⁆ * t⁻¹) := by
      conv_lhs => rw [ht'eq]
      rw [comm_mul_right]
    have hX : t * ⁅w, t⁻¹ * t'⁆ * t⁻¹ ∈ dsFrattini Q :=
      frattiniChief_conj_mem Q ht (comm_mem_frat hQ hwQ hcos)
    have hY : ⁅w, t⁆ = ⁅w, t'⁆ * (t * ⁅w, t⁻¹ * t'⁆ * t⁻¹)⁻¹ := by
      rw [hkey]
      group
    rw [hY]
    exact (dsFrattini Q).mul_mem (hW''_t' w hw) ((dsFrattini Q).inv_mem hX)
  have hB6 : ∀ x ∈ Q, ⁅x, t⁆ ∈ dsFrattini Q := by
    intro x hx
    have hx' : x ∈ W' ⊔ W'' := by rw [hsup]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hW''N).1 hx'
    have ha_N : a ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer (hW'Q ha)
    have hcon : a * ⁅b, t⁆ * a⁻¹ ∈ dsFrattini Q := frattiniChief_conj_mem Q ha_N (hB5 b hb)
    rw [comm_mul_left]
    exact (dsFrattini Q).mul_mem hcon (hW'_t a ha)
  apply htQ
  apply hburn
  intro q hq
  rw [← commutatorElement_inv]
  exact (dsFrattini Q).inv_mem (hB6 q hq)

theorem exists_order_three {L : Subgroup G} [Finite G] (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    ∃ k ∈ L, orderOf k = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : (finRotate 3) ^ 3 = 1 := by decide
  have hc1 : finRotate 3 ≠ 1 := by decide
  have hcord : orderOf (finRotate 3) = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm (finRotate 3))
  have hgord : orderOf (QuotientGroup.mk g : oTwoQuot ↥L) = 3 := by
    have h3 : orderOf (e.symm (finRotate 3)) = orderOf (finRotate 3) :=
      MulEquiv.orderOf_eq e.symm (finRotate 3)
    rw [hg, h3, hcord]
  have hdvd : 3 ∣ orderOf g := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L)) g
    rw [QuotientGroup.mk'_apply, hgord] at h
    exact h
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨((g ^ (orderOf g / 3) : ↥L) : G), (g ^ (orderOf g / 3)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div hpos hdvd

theorem le_of_comm_mem [Finite G] {Q M : Subgroup G} (hQ : IsPGroup 2 Q) {k : G}
    (hk : k ∈ Subgroup.normalizer (Q : Set G)) (hfix : FixFree (dsFrattini Q) Q k)
    (hQc : Nat.card Q = 64) (hΦc : Nat.card (dsFrattini Q) = 4) (hM : M ≤ Q)
    (hcomm : ∀ q ∈ Q, ⁅q, k⁆ ∈ M) : Q ≤ M := by
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hQ⟩
  have hcQ : ∀ x ∈ Q, ⁅x, k⁆ ∈ Q := by
    intro x hx
    rw [commutatorElement_def]
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact Q.mul_mem hx (conj_mem_of_mem_normalizer' hk (Q.inv_mem hx))
  let cm : ↥Q → ↥Q := fun x => ⟨⁅(x : G), k⁆, hcQ x x.2⟩
  let N : Subgroup ↥Q := frattini ↥Q
  have hcm_val : ∀ x : ↥Q, ((cm x : ↥Q) : G) = ⁅(x : G), k⁆ := fun x => rfl
  have hcomm_N : ∀ a b : ↥Q, ⁅a, b⁆ ∈ N := by
    intro a b
    exact CFSG.commutator_le_frattini_of_isPGroup (p := 2) (R := ↥Q)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have hmem_frat : ∀ y : ↥Q, y ∈ N ↔ (y : G) ∈ dsFrattini Q := by
    intro y
    constructor
    · intro hy
      exact Subgroup.mem_map_of_mem Q.subtype hy
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      have : z = y := Subtype.ext hzy
      rw [← this]
      exact hz
  have hquot_comm : ∀ a b : ↥Q, (QuotientGroup.mk a : ↥Q ⧸ N) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    intro a b
    have h := (QuotientGroup.eq_one_iff (⁅a, b⁆ : ↥Q)).mpr (hcomm_N a b)
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
    calc (QuotientGroup.mk a : ↥Q ⧸ N) * QuotientGroup.mk b
        = (QuotientGroup.mk a * QuotientGroup.mk b * (QuotientGroup.mk a)⁻¹ *
            (QuotientGroup.mk b)⁻¹) * (QuotientGroup.mk b * QuotientGroup.mk a) := by group
      _ = QuotientGroup.mk b * QuotientGroup.mk a := by rw [h, one_mul]
  have hcy : ∀ x y : ↥Q, cm (x * y) = ⁅x, cm y⁆ * (cm y * cm x) := by
    intro x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, commutatorElement_def, hcm_val]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcm_val, commutatorElement_def]
    group
  let φ : ↥Q →* ↥Q ⧸ N := MonoidHom.mk' (fun x => (QuotientGroup.mk (cm x) : ↥Q ⧸ N)) (by
    intro x y
    rw [hcy x y, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    rw [(QuotientGroup.eq_one_iff ⁅x, cm y⁆).mpr (hcomm_N x (cm y)), one_mul]
    exact hquot_comm (cm y) (cm x))
  have hφ : ∀ x, φ x = (QuotientGroup.mk (cm x) : ↥Q ⧸ N) := fun x => rfl
  have hker : φ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h1 : ⁅(x : G), k⁆ ∈ dsFrattini Q := (hmem_frat (cm x)).mp h
      exact (hmem_frat x).mpr (hfix (x : G) x.2 h1)
    · intro h
      have hx : (x : G) ∈ dsFrattini Q := (hmem_frat x).mp h
      rw [hmem_frat, hcm_val, commutatorElement_def]
      have e : (x : G) * k * (x : G)⁻¹ * k⁻¹ = (x : G) * (k * (x : G)⁻¹ * k⁻¹) := by group
      rw [e]
      exact (dsFrattini Q).mul_mem hx (frattiniChief_conj_mem Q hk ((dsFrattini Q).inv_mem hx))
  have hNc : Nat.card N = 4 := by
    rw [← hΦc]
    exact (Subgroup.card_map_of_injective Q.subtype_injective).symm
  have hquotc : Nat.card (↥Q ⧸ N) = 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNc] at h
    have h' : Nat.card ↥Q = 64 := hQc
    omega
  have hr : Nat.card (↥Q ⧸ N) = Nat.card φ.range := by
    have := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hker] at this
    exact this
  have hrange : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hr.symm
  have hcover : ∀ x ∈ Q, x ∈ M ⊔ dsFrattini Q := by
    intro x hx
    have hy : (QuotientGroup.mk (⟨x, hx⟩ : ↥Q) : ↥Q ⧸ N) ∈ φ.range := by
      rw [hrange]
      exact Subgroup.mem_top _
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hy
    rw [hφ] at hz
    have hmem : (cm z)⁻¹ * ⟨x, hx⟩ ∈ N := QuotientGroup.eq.mp hz
    have hΦ : (((cm z)⁻¹ * ⟨x, hx⟩ : ↥Q) : G) ∈ dsFrattini Q := (hmem_frat _).mp hmem
    have hx_eq : x = ⁅(z : G), k⁆ * (((cm z)⁻¹ * ⟨x, hx⟩ : ↥Q) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcm_val, Subgroup.coe_mk]
      group
    rw [hx_eq]
    exact (M ⊔ dsFrattini Q).mul_mem (Subgroup.mem_sup_left (hcomm (z : G) z.2))
      (Subgroup.mem_sup_right hΦ)
  have hQM : M ⊔ dsFrattini Q = Q := by
    apply le_antisymm (sup_le hM (Subgroup.map_subtype_le _))
    intro x hx
    exact hcover x hx
  exact DSBA5.le_of_sup_dsFrattini_eq hM hQM

end DSJ2

namespace DSJ2

variable {G : Type} [Group G]

theorem dsOmega1_centerOf_le (X : Subgroup G) : dsOmega1 (centerOf X) ≤ X := by
  unfold dsOmega1
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact (hx.1).1

theorem dsOmega1_le_centralizer (X : Subgroup G) :
    dsOmega1 (centerOf X) ≤ Subgroup.centralizer (X : Set G) := by
  unfold dsOmega1
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
    have := Subgroup.mem_centralizer_iff.mp (hx.1).2 g hg
    exact this

theorem le_normalizer_inf' {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  have hA' := Subgroup.mem_normalizer_iff.mp (hA hg) x
  have hB' := Subgroup.mem_normalizer_iff.mp (hB hg) x
  exact and_congr hA' hB'

end DSJ2

open DSJ2

theorem leafDSBJQ2 [DSLeaf LeafDSBJQ1] [DSLeaf LeafDSBJV1] [DSLeaf LeafDSBJZ2] [DSLeaf LeafDSBS3Vertex] [DSLeaf LeafM3] [DSLeaf LeafM5] [DSLeaf LeafM7] [DSLeaf LeafZiStructure] [DSLeaf LeafRankBounds] [DSLeaf LeafFrattiniChief] : LeafDSBJQ2 := by
  intro G _ _ L1 L2 S h cJ
  obtain ⟨hQ1eq, hO2L1, hQ8⟩ := dsbjq1 h cJ
  obtain ⟨hZcard, hA5, hNat, -, -⟩ := dsbjv1 h cJ
  obtain ⟨⟨-, -⟩, ⟨hZ2eq, hfixk, hZ2card', -, hdZ2⟩, hZ2Q1⟩ := dsbjz2 h cJ
  obtain ⟨hSsplit, hrelQ, hcentS3, hQcard⟩ := dsbs3_vertex h
  have hZSet : ZSetting L1 L2 S := ⟨h.hyp, DSBHyp.bnorm h⟩
  have hZSet2 : ZSetting L2 L1 S := ZSetting.symm hZSet
  obtain ⟨-, hZle2, -, -, -, hP2Z2, -⟩ := zi_structure hZSet2
  have hpc1 : Nat.card ↥(pCoreOf 2 L1) = 32 := hQ8.1
  have hQ1card : Nat.card ↥(dsQ L1 L2 S) = 32 := by rw [← hO2L1]; exact hpc1
  have hZc : Nat.card ↥(dsZ S) = 2 := hZcard
  have hZ2c : Nat.card ↥(dsZi L2 S) = 4 := by rw [hZ2card', hZc]; norm_num
  have hQc : Nat.card ↥(dsQ L2 L1 S) = 64 := by rw [hQcard, hQ1card]
  have hQS : dsQ L2 L1 S ≤ S := le_sup_right.trans hSsplit.ge
  have hSc : Nat.card ↥S = 128 := by
    have := relIndex_mul_card_of_le hQS
    rw [hrelQ, hQc] at this
    omega
  have hA5par : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hq1 : IsL2Quot 2 (oTwoQuot ↥L1) := hA5par.quot
  have hsylS1 : IsSylowTwoOf (S ⊓ L1) L1 := h.hyp.hyp.h1.sylow
  obtain ⟨⟨d, hdB, hd3⟩, hcard4⟩ := DSBA5.three_and_card hsylS1 hq1
  have hSL1 : S ⊓ L1 = S := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [hcard4, hpc1, hSc]
  have hSyl : IsSylowTwoOf S L1 := by
    rw [← hSL1]
    exact hsylS1
  have hpcS : pCoreOf 2 L1 ≤ S := (F7.isSylowTwoOf_pCoreOf_le hsylS1).trans inf_le_left
  have hQ1S : dsQ L1 L2 S ≤ S := (le_of_eq hO2L1.symm).trans hpcS
  have hm5 := (m5 hq1 hSyl).1
  have hBor : ∀ g ∈ L1 ⊓ Subgroup.normalizer (S : Set G), g ∈ borelOf L1 S := by
    intro g hg
    unfold borelOf
    rw [hSL1]
    exact hg
  have hBP2 : ∀ g ∈ borelOf L1 S, g ∈ L2 ⊔ bigB L2 L1 S := by
    intro g hg
    have hgB : g ∈ bigB L1 L2 S := (le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hg
    rw [bigB_comm L1 L2 S]
    exact (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hgB
  have hP2N : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (L2 : Set G) :=
    F1.parabolic_le_normalizer h.hyp.symm
  have hP2char : CharTwo (L2 ⊔ bigB L2 L1 S) := F1.parabolic_charTwo h.hyp.symm
  have hQP2 : dsQ L2 L1 S ≤ L2 ⊔ bigB L2 L1 S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQN : L2 ⊔ bigB L2 L1 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hSP2 : S ≤ L2 ⊔ bigB L2 L1 S :=
    hSsplit.trans_le (sup_le (inf_le_right.trans le_sup_left) hQP2)
  have hQ2 : IsPGroup 2 (dsQ L2 L1 S) := CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 _
  have hQ1Q : dsQ L1 L2 S ⊔ dsQ L2 L1 S = S := by
    have hN1 : L1 ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) :=
      fun g hg => by
        rw [← hO2L1]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1 hg.1
    have hN2 : L1 ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) :=
      fun g hg => hQN (hBP2 g (hBor g hg))
    have hX := hm5 (dsQ L1 L2 S ⊔ dsQ L2 L1 S) (le_sup_of_le_left (le_of_eq hO2L1))
      (sup_le hQ1S hQS) (F1.le_normalizer_sup hN1 hN2)
    rcases hX with hX | hX
    · exfalso
      have hle : dsQ L2 L1 S ≤ pCoreOf 2 L1 := (le_sup_right.trans hX.le)
      have := Subgroup.card_le_of_le hle
      omega
    · exact hX
  have hex_t : ∃ t ∈ S ⊓ L2, t ∉ dsQ L2 L1 S := by
    by_contra hcon
    push Not at hcon
    have hSQ : S ≤ dsQ L2 L1 S := hSsplit.trans_le (sup_le (fun t ht => hcon t ht) le_rfl)
    have := Subgroup.card_le_of_le hSQ
    omega
  have hex_t' : ∃ t' ∈ dsQ L1 L2 S, t' ∉ dsQ L2 L1 S := by
    by_contra hcon
    push Not at hcon
    have hle : dsQ L1 L2 S ⊔ dsQ L2 L1 S ≤ dsQ L2 L1 S :=
      sup_le (fun t ht => hcon t ht) le_rfl
    rw [hQ1Q] at hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨t, htSL2, htQ⟩ := hex_t
  obtain ⟨t', ht'Q1, ht'Q⟩ := hex_t'
  have htS : t ∈ S := (inf_le_left : S ⊓ L2 ≤ S) htSL2
  have htL2 : t ∈ L2 := (inf_le_right : S ⊓ L2 ≤ L2) htSL2
  have ht'S : t' ∈ S := hQ1S ht'Q1
  have hcos : t⁻¹ * t' ∈ dsQ L2 L1 S := mem_of_index_two hrelQ htS ht'S htQ ht'Q
  obtain ⟨e3⟩ := h.s3
  obtain ⟨k, hkL2, hk3⟩ := exists_order_three e3
  have hkP2 : k ∈ L2 ⊔ bigB L2 L1 S := (le_sup_left : L2 ≤ L2 ⊔ bigB L2 L1 S) hkL2
  have hkN : k ∈ Subgroup.normalizer (dsQ L2 L1 S : Set G) := hQN hkP2
  have hdP2 : d ∈ L2 ⊔ bigB L2 L1 S := hBP2 d hdB
  have hdN : d ∈ Subgroup.normalizer (dsQ L2 L1 S : Set G) := hQN hdP2
  have hS3 : S3Par L2 (L2 ⊔ bigB L2 L1 S) d :=
    ⟨le_sup_left, hP2N, hP2char, h.s3, hdP2, hd3, fun l hl => hcentS3 d hdB hd3 l hl⟩
  obtain ⟨hΦ16, -, hT⟩ := m7 hS3 hkL2 hk3
  have hΦle : dsFrattini (dsQ L2 L1 S) ≤ dsQ L2 L1 S := Subgroup.map_subtype_le _
  have hΦc : Nat.card ↥(dsFrattini (dsQ L2 L1 S)) = 4 := by
    have h1 := relIndex_mul_card_of_le hΦle
    have h16 : (dsFrattini (dsQ L2 L1 S)).relIndex (dsQ L2 L1 S) = 16 := hΦ16
    rw [h16, hQc] at h1
    omega
  rcases hT with hT2 | hT1
  ·
    have hFix : FixFree (dsFrattini (dsQ L2 L1 S)) (dsQ L2 L1 S) k := hT2.1
    have hcomm : ∀ q ∈ dsQ L2 L1 S, ⁅q, k⁆ ∈ L2 ⊓ dsQ L2 L1 S := by
      intro q hq
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact L2.mul_mem (conj_mem_of_mem_normalizer' (hP2N (hQP2 hq)) hkL2) (L2.inv_mem hkL2)
      · rw [commutatorElement_def]
        have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
        rw [e]
        exact (dsQ L2 L1 S).mul_mem hq
          (conj_mem_of_mem_normalizer' hkN ((dsQ L2 L1 S).inv_mem hq))
    have hQL2 : dsQ L2 L1 S ≤ L2 :=
      (le_of_comm_mem hQ2 hkN hFix hQc hΦc inf_le_right hcomm).trans inf_le_left
    have hpcL2 : pCoreOf 2 L2 = dsQ L2 L1 S := by
      have h1 := F1.inf_pCoreOf_parabolic_eq h.hyp.symm
      rw [← h1]
      exact inf_eq_left.mpr hQL2
    refine ⟨hpcL2, ?_⟩
    rw [hpcL2, hQc]
    norm_num
  ·
    exfalso
    obtain ⟨W', W'', hΦW', hW'Q, hΦW'', hW''Q, hPW', hPW'', hinf, hsup, hrelW', hrelW'',
      hL2W', hfixW', hdW'', hfixW'', hnt⟩ := hT1
    have hZ2Q : dsZi L2 S ≤ dsQ L2 L1 S := by
      rw [hZ2eq]
      exact dsOmega1_centerOf_le _
    have hZ2central : ∀ z ∈ dsZi L2 S, ∀ q ∈ dsQ L2 L1 S, q * z = z * q := by
      intro z hz q hq
      rw [hZ2eq] at hz
      exact Subgroup.mem_centralizer_iff.mp (dsOmega1_le_centralizer _ hz) q hq
    have hZ2d : ∀ z ∈ dsZi L2 S, ⁅d, z⁆ = 1 := fun z hz => hdZ2 d hdB hd3 z hz
    have hkZ : k ∈ Subgroup.normalizer (dsZi L2 S : Set G) := hP2Z2 hkP2
    have hkΦ : k ∈ Subgroup.normalizer ((dsFrattini (dsQ L2 L1 S) : Subgroup G) : Set G) :=
      le_normalizer_frat hkN
    have hcase := fix_dichotomy hkZ hkΦ (hfixk k hkL2 hk3) hZ2c
    rcases hcase with hcaseA | hcaseB
    · exact caseA_false hQ2 hdN hZ2Q hZ2central hZ2d hZ2c hZ2eq hQc hΦc (hQP2.trans hPW')
        hsup hΦW' hΦW'' hrelW' hrelW'' hfixW' hdW'' hcaseA
    ·
      have hZ2Φ : dsZi L2 S = dsFrattini (dsQ L2 L1 S) :=
        Subgroup.eq_of_le_of_card_ge hcaseB (by rw [hZ2c, hΦc])
      have hA5' : A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) (dsZ S) := by
        rw [hQ1eq]
        exact hA5
      have hNat' : ¬ NatSec L1 (dsZ S) (dsQ L1 L2 S) := by
        rw [hQ1eq]
        exact hNat
      obtain ⟨hcls, hrelF1, -, -, hfixpt, hfpf⟩ := (m3 hA5' hSyl).2 hNat'
      set F1 := ⁅⁅dsQ L1 L2 S, S⁆, S⁆ ⊔ dsZ S with hF1def
      have hZF1 : dsZ S ≤ F1 := le_sup_right
      have hF1c : Nat.card ↥F1 = 4 := by
        have h1 := relIndex_mul_card_of_le hZF1
        rw [hrelF1, hZc] at h1
        omega
      have hrelZ : (dsZ S).relIndex (dsZi L2 S) = 2 := by
        have h1 := relIndex_mul_card_of_le (dsZ_le_dsZi L2 S)
        rw [hZc, hZ2c] at h1
        omega
      have hZ2F1 : dsZi L2 S ≤ F1 := by
        intro e he
        apply hfixpt e (hZ2Q1 he)
        intro t' ht'
        exact comm_mem_of_index_two hrelZ (hP2Z2 (hSP2 ht'))
          (fun z hz => Subgroup.mem_centralizer_iff.mp (dsOmega1_le_centralizer S hz) t' ht') he
      have hZ2eqF1 : dsZi L2 S = F1 := Subgroup.eq_of_le_of_card_ge hZ2F1 (by rw [hF1c, hZ2c])
      have hF1Φ : F1 = dsFrattini (dsQ L2 L1 S) := hZ2eqF1.symm.trans hZ2Φ
      have hL1N : L1 ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := fun g hg => by
        rw [← hO2L1]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1 hg
      have hSL1le : S ≤ L1 := hSL1.symm.trans_le inf_le_right
      have hdLN : d ∈ L1 ⊓ Subgroup.normalizer (S : Set G) := by
        have h1 := hdB
        unfold borelOf at h1
        rw [hSL1] at h1
        exact h1
      have hXcls : ∀ w ∈ W'', ⁅w, t'⁆ ∈ dsFrattini (dsQ L2 L1 S) := by
        intro w hw
        have hwQ : w ∈ dsQ L2 L1 S := hW''Q hw
        have hwS : w ∈ S := hQS hwQ
        have ht'P2 : t' ∈ L2 ⊔ bigB L2 L1 S := hSP2 ht'S
        have hx1 : ⁅w, t'⁆ ∈ dsQ L1 L2 S := by
          rw [commutatorElement_def]
          have e : w * t' * w⁻¹ * t'⁻¹ = (w * t' * w⁻¹) * t'⁻¹ := rfl
          rw [e]
          exact (dsQ L1 L2 S).mul_mem (conj_mem_of_mem_normalizer' (hL1N (hSL1le hwS)) ht'Q1)
            ((dsQ L1 L2 S).inv_mem ht'Q1)
        have hx2 : ⁅w, t'⁆ ∈ dsQ L2 L1 S := by
          rw [commutatorElement_def]
          have e : w * t' * w⁻¹ * t'⁻¹ = w * (t' * w⁻¹ * t'⁻¹) := by group
          rw [e]
          exact (dsQ L2 L1 S).mul_mem hwQ
            (conj_mem_of_mem_normalizer' (hQN ht'P2) ((dsQ L2 L1 S).inv_mem hwQ))
        have hx3 : ⁅w, t'⁆ ∈ W'' := by
          rw [commutatorElement_def]
          have e : w * t' * w⁻¹ * t'⁻¹ = w * (t' * w⁻¹ * t'⁻¹) := by group
          rw [e]
          exact W''.mul_mem hw (conj_mem_of_mem_normalizer' (hPW'' ht'P2) (W''.inv_mem hw))
        have hXN : L1 ⊓ Subgroup.normalizer (S : Set G) ≤
            Subgroup.normalizer ((dsQ L1 L2 S ⊓ dsQ L2 L1 S : Subgroup G) : Set G) :=
          le_normalizer_inf' (fun g hg => hL1N hg.1)
            (fun g hg => hQN (hBP2 g (hBor g hg)))
        have hX1 : dsZ S ≤ dsQ L1 L2 S ⊓ dsQ L2 L1 S :=
          le_inf hA5'.sec.1 ((dsZ_le_dsZi L2 S).trans hZ2Q)
        have hmem : ⁅w, t'⁆ ∈ dsQ L1 L2 S ⊓ dsQ L2 L1 S := ⟨hx1, hx2⟩
        rcases hcls (dsQ L1 L2 S ⊓ dsQ L2 L1 S) hX1 inf_le_left hXN with hX | hX | hX | hX
        · rw [hX] at hmem
          exact hF1Φ ▸ hZF1 hmem
        · rw [hX] at hmem
          exact hF1Φ ▸ hmem
        · rw [hX] at hmem
          have hfp := hfpf d hdLN hd3 ⁅w, t'⁆ hmem (by
            rw [← commutatorElement_inv]
            rw [hF1Φ]
            exact (dsFrattini (dsQ L2 L1 S)).inv_mem (hdW'' _ hx3))
          exact hF1Φ ▸ hfp
        · exfalso
          apply ht'Q
          exact (inf_eq_left.mp hX) ht'Q1
      exact caseB_false hQ2 (hQN (hSP2 htS)) htQ hcos hsup (hQP2.trans hPW')
        (fun w hw => by
          rw [← commutatorElement_inv]
          exact (dsFrattini (dsQ L2 L1 S)).inv_mem (hL2W' t htL2 w hw))
        hXcls (fun hq => leafFrattiniFaithful hP2char t (hSP2 htS) hq)

end CFSG.GH74.QTGen4.DSGen4
