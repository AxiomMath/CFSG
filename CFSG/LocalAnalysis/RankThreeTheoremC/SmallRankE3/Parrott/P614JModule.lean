module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614J

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.QuasithinUnique.Setup.Family (GL32)

variable {G : Type} [Group G]

theorem mem_centralizer_zpowers_iff {z g : G} :
    g ∈ centralizer (zpowers z : Set G) ↔ z * g = g * z := by
  constructor
  · intro h
    exact mem_centralizer_iff.mp h z (mem_zpowers z)
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left h k).eq

theorem centralizer_zpowers_eq (z : G) :
    centralizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem le_normalizer_of_conj_mem {K Y : Subgroup G}
    (h : ∀ k ∈ K, ∀ g ∈ Y, k * g * k⁻¹ ∈ Y) : K ≤ normalizer (Y : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h k hk g, fun hg => ?_⟩
  have h1 := h k⁻¹ (K.inv_mem hk) _ hg
  have h2 : k⁻¹ * (k * g * k⁻¹) * k⁻¹⁻¹ = g := by group
  rwa [h2] at h1

theorem normalizer_le_normalizer_centralizer (W : Subgroup G) :
    normalizer (W : Set G) ≤ normalizer (centralizer (W : Set G) : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg c hc => ?_
  rw [mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : g⁻¹ * w * g ∈ W := (mem_normalizer_iff''.mp hg w).mp hw
  have h1 := hc _ hw'
  calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * w := by group

theorem eq_one_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) {g : G} (hg : g ∈ X)
    (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hk] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · rw [h] at hk
    exact orderOf_eq_one_iff.mp hk
  · have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at h
    have h2 : 2 ∣ 3 := by
      rw [← h]
      exact dvd_pow_self 2 hk0
    norm_num at h2

theorem relIndex_centralizer_ne_two {W : Subgroup G} {z : G} (hW : IsElemAbelian 2 W)
    (hzW : z ∈ normalizer (W : Set G)) (hz3 : z ^ 3 = 1) :
    (centralizer (zpowers z : Set G)).relIndex W ≠ 2 := by
  intro h2
  rw [Subgroup.relIndex_eq_two_iff] at h2
  obtain ⟨a, haW, ha⟩ := h2
  set C : Subgroup G := centralizer (zpowers z : Set G) with hC
  have hsq : ∀ w ∈ W, w * w = 1 := fun w hw => by rw [← sq]; exact hW.2 w hw
  have hx : ∀ x ∈ W, (x * a ∈ C ∨ x ∈ C) ∧ ¬ (x * a ∈ C ∧ x ∈ C) := fun x hx =>
    (xor_iff_or_and_not_and _ _).mp (ha x hx)
  have haC : a ∉ C := fun h => (hx a haW).2 ⟨by rw [hsq a haW]; exact one_mem _, h⟩
  have hw'W : z * a * z⁻¹ ∈ W := (mem_normalizer_iff.mp hzW a).mp haW
  have hw'C : z * a * z⁻¹ ∉ C := by
    intro h
    apply haC
    have h' : z * (z * a * z⁻¹) = (z * a * z⁻¹) * z := mem_centralizer_zpowers_iff.mp h
    refine mem_centralizer_zpowers_iff.mpr ?_
    calc z * a = z⁻¹ * (z * (z * a * z⁻¹)) * z := by group
      _ = z⁻¹ * ((z * a * z⁻¹) * z) * z := by rw [h']
      _ = a * z := by group
  set c : G := z * a * z⁻¹ * a with hcdef
  have hcC : c ∈ C := ((hx _ hw'W).1.resolve_right hw'C)
  have hcW : c ∈ W := W.mul_mem hw'W haW
  have hza : z * a * z⁻¹ = c * a := by
    rw [hcdef, mul_assoc (z * a * z⁻¹) a a, hsq a haW, mul_one]
  have hcz : z * c = c * z := mem_centralizer_zpowers_iff.mp hcC
  have hcc : c * c = 1 := hsq c hcW
  have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
  have e : z * (c * a) * z⁻¹ = c * (z * a * z⁻¹) := by
    rw [← mul_assoc z c a, hcz]
    group
  have hac : a = c * a :=
    calc a = (z * z * z) * a * (z * z * z)⁻¹ := by rw [hz3']; group
      _ = z * (z * (z * a * z⁻¹) * z⁻¹) * z⁻¹ := by group
      _ = z * (z * (c * a) * z⁻¹) * z⁻¹ := by rw [hza]
      _ = z * (c * (z * a * z⁻¹)) * z⁻¹ := by rw [e]
      _ = z * (c * (c * a)) * z⁻¹ := by rw [hza]
      _ = z * a * z⁻¹ := by rw [← mul_assoc c c, hcc, one_mul]
      _ = c * a := hza
  have hc1 : c = 1 := by
    have h := hac
    nth_rewrite 1 [← one_mul a] at h
    exact (mul_right_cancel h).symm
  have hfix : z * a * z⁻¹ = a := by rw [hza, hc1, one_mul]
  apply haC
  refine mem_centralizer_zpowers_iff.mpr ?_
  calc z * a = z * a * z⁻¹ * z := by group
    _ = a * z := by rw [hfix]

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (h : E ≤ F) (hF : IsElemAbelian p F) :
    IsElemAbelian p E :=
  ⟨IsMulCommutative.of_setLike_mul_comm fun _ ha _ hb =>
    CFSG.Open.IsElemAbelian.comm hF (h ha) (h hb), fun x hx => hF.2 x (h hx)⟩

section Finite

variable [Finite G]

theorem eq_of_le_of_mem {M H K : Subgroup G} {z : G} (hK : PComp 3 M H K z)
    (hcore : rankThreePrimeCore 3 H = pCoreOf 2 H) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∀ N : Subgroup G, N ≤ K → K ≤ normalizer (N : Set G) → z ∈ N → N = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N hNK hKN hzN
  set D : Subgroup G := K ⊓ pCoreOf 2 H with hD
  have hDp : IsPGroup 2 D := (pCoreOf_isPGroup 2 H).to_le inf_le_right
  have hKD : K ≤ normalizer (D : Set G) :=
    (le_inf le_normalizer (hK.le.trans (localGroup_le_normalizer_pCoreOf 2 H))).trans
      inf_normalizer_le_normalizer_inf
  have hND : N ⊔ D ≤ K := sup_le hNK inf_le_left
  have hKND : K ≤ normalizer ((N ⊔ D : Subgroup G) : Set G) :=
    (le_inf hKN hKD).trans (inf_normalizer_le_normalizer_sup N D)
  have hmax := hK.maximal (N ⊔ D) hND
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr hKND)
    (by rw [hcore]; exact le_sup_right)
  rw [hcore] at hmax
  have hzD : z ∉ D := fun h => hz1 (eq_one_of_isPGroup_two hDp h hz3)
  have hNDK : N ⊔ D = K := hmax.resolve_left fun h =>
    hzD (show z ∈ K ⊓ pCoreOf 2 H from h ▸ (le_sup_left : N ≤ N ⊔ D) hzN)
  have hNn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have htop : D.subgroupOf K ⊔ N.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hNK, sup_comm, hNDK, Subgroup.subgroupOf_self]
  have hidx : N.relIndex K = (N.subgroupOf K).relIndex (D.subgroupOf K) := by
    have h1 : (N.subgroupOf K).relIndex (D.subgroupOf K ⊔ N.subgroupOf K) =
        (N.subgroupOf K).relIndex (D.subgroupOf K) := Subgroup.relIndex_sup_right _ _
    rw [← h1, htop, Subgroup.relIndex_top_right]
    rfl
  have hDp' : IsPGroup 2 ↥(D.subgroupOf K) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hDp'
  have hdvd : N.relIndex K ∣ 2 ^ m := by
    rw [hidx, ← hm]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact le_antisymm hNK (Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow
    Nat.prime_two hNK hKN hk le_rfl hK.perfect)

theorem exists_minimal_invariant {Q K : Subgroup G} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hKQ : K ≤ normalizer (Q : Set G)) :
    ∃ W : Subgroup G, W ≤ omegaCenter Q ∧ W ≠ ⊥ ∧ K ≤ normalizer (W : Set G) ∧
      ∀ U : Subgroup G, U ≤ W → K ≤ normalizer (U : Set G) → U = ⊥ ∨ U = W := by
  have h0 : omegaCenter Q ≤ omegaCenter Q ∧ omegaCenter Q ≠ ⊥ ∧
      K ≤ normalizer (omegaCenter Q : Set G) :=
    ⟨le_rfl, omegaCenter_ne_bot hQ hQ1, hKQ.trans (normalizer_le_normalizer_omegaCenter Q)⟩
  obtain ⟨W, hW⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Subgroup G => U ≤ omegaCenter Q ∧ U ≠ ⊥ ∧ K ≤ normalizer (U : Set G)) ⟨_, h0⟩
  refine ⟨W, hW.prop.1, hW.prop.2.1, hW.prop.2.2, fun U hUW hKU => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · exact Or.inr (hW.eq_of_le ⟨hUW.trans hW.prop.1, hU, hKU⟩ hUW)

theorem relIndex_centralizer_eq_four {Q W : Subgroup G} {z : G} (hQ : IsPGroup 2 Q)
    (hWQ : W ≤ Q) (hW : IsElemAbelian 2 W) (hzW : z ∈ normalizer (W : Set G)) (hz3 : z ^ 3 = 1)
    (hzW' : ¬ ∀ w ∈ W, z * w = w * z)
    (hind : (centralizer (zpowers z : Set G)).relIndex Q = 4) :
    (centralizer (zpowers z : Set G)).relIndex W = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (centralizer (zpowers z : Set G)).relIndex W ≤ 4 := by
    rw [← hind]
    exact Subgroup.relIndex_le_of_le_right hWQ (by rw [hind]; norm_num)
  have hdvd : (centralizer (zpowers z : Set G)).relIndex W ∣ Nat.card W :=
    Subgroup.relIndex_dvd_card _ _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hQ.to_le hWQ)
  rw [hn] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h1 : (centralizer (zpowers z : Set G)).relIndex W ≠ 1 := fun h =>
    hzW' fun w hw => mem_centralizer_zpowers_iff.mp (Subgroup.relIndex_eq_one.mp h hw)
  have h2 := relIndex_centralizer_ne_two hW hzW hz3
  rw [hj] at hle h1 h2 ⊢
  have hj2 : j ≤ 2 := by
    by_contra hj2
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases j <;> simp_all

theorem commutator_mem_of_relIndex_eq {Q W : Subgroup G} {z : G} (hWQ : W ≤ Q)
    (hWc : W ≤ centralizer (Q : Set G)) (hzW : z ∈ normalizer (W : Set G))
    (hind : (centralizer (zpowers z : Set G)).relIndex Q = 4)
    (hindW : (centralizer (zpowers z : Set G)).relIndex W = 4) :
    ∀ q ∈ Q, z * q * z⁻¹ * q⁻¹ ∈ W := by
  have hqw : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ = w := fun q hq w hw => by
    rw [mem_centralizer_iff.mp (hWc hw) q hq, mul_inv_cancel_right]
  let X : Subgroup G :=
    { carrier := {q | q ∈ Q ∧ z * q * z⁻¹ * q⁻¹ ∈ W}
      mul_mem' := by
        rintro q₁ q₂ ⟨hq₁, hw₁⟩ ⟨hq₂, hw₂⟩
        refine ⟨Q.mul_mem hq₁ hq₂, ?_⟩
        have e : z * (q₁ * q₂) * z⁻¹ * (q₁ * q₂)⁻¹ =
            (z * q₁ * z⁻¹ * q₁⁻¹) * (q₁ * (z * q₂ * z⁻¹ * q₂⁻¹) * q₁⁻¹) := by group
        rw [e, hqw q₁ hq₁ _ hw₂]
        exact W.mul_mem hw₁ hw₂
      one_mem' := ⟨Q.one_mem, by simp⟩
      inv_mem' := by
        rintro q ⟨hq, hw⟩
        refine ⟨Q.inv_mem hq, ?_⟩
        have e : z * q⁻¹ * z⁻¹ * q⁻¹⁻¹ = q⁻¹ * (z * q * z⁻¹ * q⁻¹)⁻¹ * q⁻¹⁻¹ := by group
        rw [e, hqw q⁻¹ (Q.inv_mem hq) _ (W.inv_mem hw)]
        exact W.inv_mem hw }
  have hWX : W ≤ X := fun w hw =>
    ⟨hWQ hw, W.mul_mem ((mem_normalizer_iff.mp hzW w).mp hw) (W.inv_mem hw)⟩
  have hCX : centralizer (zpowers z : Set G) ⊓ Q ≤ X := fun q hq => ⟨hq.2, by
    rw [mem_centralizer_zpowers_iff.mp hq.1, mul_inv_cancel_right, mul_inv_cancel]
    exact W.one_mem⟩
  set C : Subgroup G := centralizer (zpowers z : Set G) with hC
  set H₁ : Subgroup G := C ⊓ Q with hH₁
  set D : Subgroup G := W ⊔ H₁ with hD
  have hne : ∀ A B : Subgroup G, A.relIndex B ≠ 0 := fun A B =>
    Subgroup.index_ne_zero_of_finite
  have hH₁Q : H₁.relIndex Q = 4 := by rw [hH₁, Subgroup.inf_relIndex_right]; exact hind
  have h1 : C.relIndex W ≤ H₁.relIndex W := Subgroup.relIndex_le_of_le_left inf_le_left (hne _ _)
  have h2 : H₁.relIndex W ≤ H₁.relIndex D := Subgroup.relIndex_le_of_le_right le_sup_left (hne _ _)
  have h3 := Subgroup.relIndex_mul_relIndex H₁ D Q le_sup_right (sup_le hWQ inf_le_right)
  have hpos : 0 < D.relIndex Q := Nat.pos_of_ne_zero (hne _ _)
  rw [hH₁Q] at h3
  have hD1 : D.relIndex Q ≤ 1 := by nlinarith
  have hQD : Q ≤ D := Subgroup.relIndex_eq_one.mp (by omega)
  intro q hq
  exact (hQD.trans (sup_le hWX hCX) hq).2

theorem commutator_mem_of_gen {Q W K : Subgroup G} {z : G}
    (hKQ : K ≤ normalizer (Q : Set G)) (hKW : K ≤ normalizer (W : Set G)) (hzK : z ∈ K)
    (hgen : ∀ N : Subgroup G, N ≤ K → K ≤ normalizer (N : Set G) → z ∈ N → N = K)
    (hz : ∀ q ∈ Q, z * q * z⁻¹ * q⁻¹ ∈ W) :
    ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W := by
  let Y : Subgroup G :=
    { carrier := {g | g ∈ K ∧ ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ W}
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨K.mul_mem hg₁ hg₂, fun q hq => ?_⟩
        have e : g₁ * g₂ * q * (g₁ * g₂)⁻¹ * q⁻¹ =
            (g₁ * (g₂ * q * g₂⁻¹ * q⁻¹) * g₁⁻¹) * (g₁ * q * g₁⁻¹ * q⁻¹) := by group
        rw [e]
        exact W.mul_mem ((mem_normalizer_iff.mp (hKW hg₁) _).mp (h₂ q hq)) (h₁ q hq)
      one_mem' := ⟨K.one_mem, fun q _ => by simp⟩
      inv_mem' := by
        rintro g ⟨hg, h⟩
        refine ⟨K.inv_mem hg, fun q hq => ?_⟩
        have e : g⁻¹ * q * g⁻¹⁻¹ * q⁻¹ = g⁻¹ * (g * q * g⁻¹ * q⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.mp (hKW (K.inv_mem hg)) _).mp (W.inv_mem (h q hq)) }
  have hYK : Y ≤ K := fun g hg => hg.1
  have hKY : K ≤ normalizer (Y : Set G) := le_normalizer_of_conj_mem fun k hk g hg => by
    refine ⟨K.mul_mem (K.mul_mem hk hg.1) (K.inv_mem hk), fun q hq => ?_⟩
    have hq' : k⁻¹ * q * k ∈ Q := (mem_normalizer_iff''.mp (hKQ hk) q).mp hq
    have e : k * g * k⁻¹ * q * (k * g * k⁻¹)⁻¹ * q⁻¹ =
        k * (g * (k⁻¹ * q * k) * g⁻¹ * (k⁻¹ * q * k)⁻¹) * k⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hKW hk) _).mp (hg.2 _ hq')
  have hYeq := hgen Y hYK hKY ⟨hzK, hz⟩
  intro k hk q hq
  have hkY : k ∈ Y := by rw [hYeq]; exact hk
  exact hkY.2 q hq

theorem comm_of_commutator_mem {Q W K : Subgroup G} (hWc : W ≤ centralizer (Q : Set G))
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hQK : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W)
    (hV : Q ⊓ centralizer (K : Set G) = ⊥) :
    ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, q₁ * q₂ = q₂ * q₁ := by
  have hqw : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ = w := fun q hq w hw => by
    rw [mem_centralizer_iff.mp (hWc hw) q hq, mul_inv_cancel_right]
  intro q₁ hq₁ q₂ hq₂
  set c : G := q₁ * q₂ * q₁⁻¹ * q₂⁻¹ with hc
  have hcQ : c ∈ Q := Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁)) (Q.inv_mem hq₂)
  have hcK : c ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    let ψ : ↥Q →* ↥W :=
      { toFun := fun q => ⟨k * q * k⁻¹ * (q : G)⁻¹, hQK k hk q q.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          show k * ((a : G) * b) * k⁻¹ * ((a : G) * b)⁻¹ =
            (k * a * k⁻¹ * (a : G)⁻¹) * (k * b * k⁻¹ * (b : G)⁻¹)
          have e : k * ((a : G) * b) * k⁻¹ * ((a : G) * b)⁻¹ =
              (k * a * k⁻¹ * (a : G)⁻¹) * ((a : G) * (k * b * k⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
            group
          rw [e, hqw a a.2 _ (hQK k hk b b.2)]) }
    have hψc : ψ ⟨c, hcQ⟩ = 1 := by
      have hc' : (⟨c, hcQ⟩ : ↥Q) = ⟨q₁, hq₁⟩ * ⟨q₂, hq₂⟩ * ⟨q₁, hq₁⟩⁻¹ * ⟨q₂, hq₂⟩⁻¹ :=
        Subtype.ext rfl
      have hcomm : ψ ⟨q₁, hq₁⟩ * ψ ⟨q₂, hq₂⟩ = ψ ⟨q₂, hq₂⟩ * ψ ⟨q₁, hq₁⟩ :=
        Subtype.ext (hWab _ (ψ _).2 _ (ψ _).2)
      rw [hc', map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h1 : k * c * k⁻¹ * c⁻¹ = 1 := congrArg Subtype.val hψc
    calc k * c = k * c * k⁻¹ * c⁻¹ * c * k := by group
      _ = c * k := by rw [h1, one_mul]
  have h1 : c ∈ Q ⊓ centralizer (K : Set G) := ⟨hcQ, hcK⟩
  rw [hV, Subgroup.mem_bot] at h1
  calc q₁ * q₂ = c * q₂ * q₁ := by rw [hc]; group
    _ = q₂ * q₁ := by rw [h1, one_mul]

theorem mem_normalizer_of_minimal {Q W K : Subgroup G} {b : G} (hWQ : W ≤ Q) (hW1 : W ≠ ⊥)
    (hKW : K ≤ normalizer (W : Set G))
    (hirr : ∀ U : Subgroup G, U ≤ W → K ≤ normalizer (U : Set G) → U = ⊥ ∨ U = W)
    (hQK : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ W)
    (hV : Q ⊓ centralizer (K : Set G) = ⊥)
    (hbK : b ∈ normalizer (K : Set G)) (hbQ : b ∈ normalizer (Q : Set G)) :
    b ∈ normalizer (W : Set G) := by
  set U : Subgroup G := W.map (MulAut.conj b).toMonoidHom with hU
  have hUQ : U ≤ Q := by
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.mp hbQ w).mp (hWQ hw)
  have hKU : K ≤ normalizer (U : Set G) := le_normalizer_of_conj_mem fun k hk u hu => by
    obtain ⟨w, hw, rfl⟩ := hu
    have hk' : b⁻¹ * k * b ∈ K := (mem_normalizer_iff''.mp hbK k).mp hk
    refine ⟨(b⁻¹ * k * b) * w * (b⁻¹ * k * b)⁻¹, (mem_normalizer_iff.mp (hKW hk') w).mp hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKUW : K ≤ normalizer ((U ⊓ W : Subgroup G) : Set G) :=
    (le_inf hKU hKW).trans inf_normalizer_le_normalizer_inf
  rcases hirr (U ⊓ W) inf_le_right hKUW with h | h
  ·
    exfalso
    have hUc : U ≤ Q ⊓ centralizer (K : Set G) := by
      refine le_inf hUQ fun u hu => ?_
      rw [mem_centralizer_iff]
      intro k hk
      have h1 : k * u * k⁻¹ * u⁻¹ ∈ U ⊓ W :=
        ⟨U.mul_mem ((mem_normalizer_iff.mp (hKU hk) u).mp hu) (U.inv_mem hu),
          hQK k hk u (hUQ hu)⟩
      rw [h, Subgroup.mem_bot] at h1
      calc k * u = k * u * k⁻¹ * u⁻¹ * u * k := by group
        _ = u * k := by rw [h1, one_mul]
    rw [hV, le_bot_iff, hU] at hUc
    exact hW1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj b).injective).mp hUc)
  ·
    have hWU : W ≤ U := by rw [← h]; exact inf_le_left
    have hcard : Nat.card U = Nat.card W :=
      Subgroup.card_map_of_injective (MulAut.conj b).injective
    exact mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hWU hcard.le).symm

theorem commute_of_inf_centralizer_eq_bot (k3010 : KFact3010) {H K : Subgroup G} {z b : G}
    (hKQ : K ≤ normalizer (pCoreOf 2 H : Set G))
    (hV : pCoreOf 2 H ⊓ centralizer (K : Set G) = ⊥) (hzK : z ∈ K) (hz1 : z ≠ 1)
    (hz3 : z ^ 3 = 1) (hind : (centralizer (zpowers z : Set G)).relIndex (pCoreOf 2 H) = 4)
    (hgen : ∀ N : Subgroup G, N ≤ K → K ≤ normalizer (N : Set G) → z ∈ N → N = K)
    (hbK : b ∈ normalizer (K : Set G)) (hbQ : b ∈ normalizer (pCoreOf 2 H : Set G))
    (hbc : ⁅zpowers b, K⁆ ≤ pCoreOf 2 H) (hkbar : KbarA5 H K ∨ KbarL32 H K) :
    ∀ q ∈ pCoreOf 2 H, b * q = q * b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  have hQ : IsPGroup 2 Q := pCoreOf_isPGroup 2 H
  have hQ1 : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.relIndex_bot_right] at hind
    norm_num at hind
  obtain ⟨W, hWΩ, hW1, hKW, hirr⟩ := exists_minimal_invariant hQ hQ1 hKQ
  have hWQ : W ≤ Q := hWΩ.trans (omegaCenter_le Q)
  have hWc : W ≤ centralizer (Q : Set G) := hWΩ.trans (omegaCenter_le_centralizer Q)
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_le hWΩ (isElemAbelian_omegaCenter Q)
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    CFSG.Open.IsElemAbelian.comm hWe ha hb
  have hzW' : ¬ ∀ w ∈ W, z * w = w * z := by
    intro h
    have hN : K ⊓ centralizer (W : Set G) = K := by
      refine hgen _ inf_le_left ?_ ⟨hzK, mem_centralizer_iff.mpr fun w hw => (h w hw).symm⟩
      exact (le_inf le_normalizer (hKW.trans (normalizer_le_normalizer_centralizer W))).trans
        inf_normalizer_le_normalizer_inf
    have hKc : K ≤ centralizer (W : Set G) := inf_eq_left.mp hN
    have hWK : W ≤ Q ⊓ centralizer (K : Set G) := le_inf hWQ (Subgroup.le_centralizer_iff.mp hKc)
    rw [hV] at hWK
    exact hW1 (le_bot_iff.mp hWK)
  have hindW := relIndex_centralizer_eq_four hQ hWQ hWe (hKW hzK) hz3 hzW' hind
  have hzQ := commutator_mem_of_relIndex_eq hWQ hWc (hKW hzK) hind hindW
  have hQK := commutator_mem_of_gen hKQ hKW hzK hgen hzQ
  have hQab := comm_of_commutator_mem hWc hWab hQK hV
  have hbW := mem_normalizer_of_minimal hWQ hW1 hKW hirr hQK hV hbK hbQ
  have hc_b : ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ Q := fun k hk => by
    have h := hbc (commutator_mem_commutator (mem_zpowers b) hk)
    rwa [commutatorElement_def] at h
  have hf : (∃ f : ↥K →* alternatingGroup (Fin 5), Function.Surjective f ∧
        ∀ k : ↥K, f k = 1 → ∀ w ∈ W, (k : G) * w = w * k) ∨
      (∃ f : ↥K →* GL32, Function.Surjective f ∧
        ∀ k : ↥K, f k = 1 → ∀ w ∈ W, (k : G) * w = w * k) := by
    rcases hkbar with ⟨f, hfs, hfk⟩ | ⟨f, hfs, hfk⟩
    · exact Or.inl ⟨f, hfs, fun k hk w hw => mem_centralizer_iff.mp (hWc hw) k ((hfk k).1 hk)⟩
    · exact Or.inr ⟨f, hfs, fun k hk w hw => mem_centralizer_iff.mp (hWc hw) k ((hfk k).1 hk)⟩
  have hrel : (centralizer ({z} : Set G)).relIndex W = 4 := by
    rw [← centralizer_zpowers_eq]
    exact hindW
  have hbcomm : ∀ k ∈ K, ∀ w ∈ W, b * (k * w * k⁻¹) * b⁻¹ = k * (b * w * b⁻¹) * k⁻¹ := by
    intro k hk w hw
    have hx : k * (b * w * b⁻¹) * k⁻¹ ∈ W :=
      (mem_normalizer_iff.mp (hKW hk) _).mp ((mem_normalizer_iff.mp hbW w).mp hw)
    have e : b * (k * w * k⁻¹) * b⁻¹ =
        (b * k * b⁻¹ * k⁻¹) * (k * (b * w * b⁻¹) * k⁻¹) * (b * k * b⁻¹ * k⁻¹)⁻¹ := by group
    rw [e, mem_centralizer_iff.mp (hWc hx) _ (hc_b k hk), mul_inv_cancel_right]
  have hbWc := k3010 G W K z b hWe hKW hf hirr hzK (orderOf_eq_prime hz3 hz1) hrel hbW hbcomm
  have hcommQ : ∀ k ∈ K, ∀ q ∈ Q, b * (k * q * k⁻¹) * b⁻¹ = k * (b * q * b⁻¹) * k⁻¹ := by
    intro k hk q hq
    have hkbq : k * (b * q * b⁻¹) * k⁻¹ ∈ Q :=
      (mem_normalizer_iff.mp (hKQ hk) _).mp ((mem_normalizer_iff.mp hbQ q).mp hq)
    have e : b * (k * q * k⁻¹) * b⁻¹ =
        (b * k * b⁻¹ * k⁻¹) * (k * (b * q * b⁻¹) * k⁻¹) * (b * k * b⁻¹ * k⁻¹)⁻¹ := by group
    rw [e, hQab _ (hc_b k hk) _ hkbq, mul_inv_cancel_right]
  intro q hq
  set u : G := b * q * b⁻¹ * q⁻¹ with hu
  have huQ : u ∈ Q := Q.mul_mem ((mem_normalizer_iff.mp hbQ q).mp hq) (Q.inv_mem hq)
  have huK : u ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hw := hQK k hk q hq
    have hwQ : k * q * k⁻¹ * q⁻¹ ∈ Q := hWQ hw
    have hbw : b * (k * q * k⁻¹ * q⁻¹) * b⁻¹ = k * q * k⁻¹ * q⁻¹ := by
      rw [hbWc _ hw, mul_inv_cancel_right]
    have key : k * u * k⁻¹ = u := by
      have e1 : k * u * k⁻¹ = (k * (b * q * b⁻¹) * k⁻¹) * (k * q * k⁻¹)⁻¹ := by
        rw [hu]
        group
      rw [e1, ← hcommQ k hk q hq]
      have e2 : b * (k * q * k⁻¹) * b⁻¹ * (k * q * k⁻¹)⁻¹ =
          (b * (k * q * k⁻¹ * q⁻¹) * b⁻¹) * u * (k * q * k⁻¹ * q⁻¹)⁻¹ := by
        rw [hu]
        group
      rw [e2, hbw, hQab _ hwQ _ huQ]
      group
    calc k * u = k * u * k⁻¹ * k := by group
      _ = u * k := by rw [key]
  have hu1 : u ∈ Q ⊓ centralizer (K : Set G) := ⟨huQ, huK⟩
  rw [hV, Subgroup.mem_bot] at hu1
  calc b * q = u * q * b := by rw [hu]; group
    _ = q * b := by rw [hu1, one_mul]

end Finite

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614J
