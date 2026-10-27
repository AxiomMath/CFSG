module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDETwin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

section DeqGaschutz

open scoped commutatorElement

theorem deq2_commutator_eq_of_central {Γ : Type*} [Group Γ] {v₁ v₂ : Γ}
    (h₁ : ∀ x, v₁ * x = x * v₁) (h₂ : ∀ x, v₂ * x = x * v₂) (a b : Γ) :
    ⁅v₁ * a, v₂ * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have c1 : ∀ w, v₁ * w * v₁⁻¹ = w := fun w => by
    rw [h₁ w, mul_assoc, mul_inv_cancel, mul_one]
  have c2 : ∀ w, v₂ * w * v₂⁻¹ = w := fun w => by
    rw [h₂ w, mul_assoc, mul_inv_cancel, mul_one]
  calc v₁ * a * (v₂ * b) * (v₁ * a)⁻¹ * (v₂ * b)⁻¹
      = v₁ * (a * v₂ * b * a⁻¹) * v₁⁻¹ * b⁻¹ * v₂⁻¹ := by group
    _ = (a * v₂ * b * a⁻¹) * b⁻¹ * v₂⁻¹ := by rw [c1]
    _ = (v₂ * a * b * a⁻¹) * b⁻¹ * v₂⁻¹ := by rw [← h₂ a]
    _ = v₂ * (a * b * a⁻¹ * b⁻¹) * v₂⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := c2 _

theorem deq2_le_of_central_quotient {G : Type*} [Group G] [Finite G] {B Q X : Subgroup G}
    [B.Normal] (hBQ : B ≤ Q) (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ g : G, ∀ q ∈ Q, QuotientGroup.mk' B g * QuotientGroup.mk' B q =
        QuotientGroup.mk' B q * QuotientGroup.mk' B g)
    (hperf : (⊤ : Subgroup G) ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
    (S : Sylow 2 G) (hXS : X ≤ (S : Subgroup G)) (hXQ : Q ⊓ X ≤ B)
    (hQX : Q ⊔ X = (S : Subgroup G)) : Q ≤ B := by
  classical
  have hπ : Function.Surjective (QuotientGroup.mk' B) := QuotientGroup.mk'_surjective B
  set π : G →* G ⧸ B := QuotientGroup.mk' B with hπdef
  set V : Subgroup (G ⧸ B) := Q.map π with hV
  have hVc : ∀ v ∈ V, ∀ g : G ⧸ B, v * g = g * v := by
    intro v hv g
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨g, rfl⟩ := hπ g
    exact (hcent g q hq).symm
  haveI hVn : V.Normal := ⟨fun n hn g => by
    rw [← hVc n hn g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  haveI hVc' : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVc a.1 a.2 b.1)⟩⟩
  have hV2 : IsPGroup 2 V := hQ2.map π
  let P' : Sylow 2 (G ⧸ B) := S.mapSurjective hπ
  have hP' : (P' : Subgroup (G ⧸ B)) = (S : Subgroup G).map π := Sylow.coe_mapSurjective hπ S
  have hle : X.map π ≤ (P' : Subgroup (G ⧸ B)) := by
    rw [hP']; exact Subgroup.map_mono hXS
  have hinf : V ⊓ X.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, hyX⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hyV
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hyX
    have h1 : x⁻¹ * q ∈ B := (QuotientGroup.eq).mp hxq
    have hxQ : x ∈ Q := by
      have : x⁻¹ ∈ Q := by
        have h2 : x⁻¹ * q * q⁻¹ ∈ Q := Q.mul_mem (hBQ h1) (Q.inv_mem hq)
        simpa using h2
      simpa using Q.inv_mem this
    have hxB : x ∈ B := hXQ ⟨hxQ, hx⟩
    have : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hxB
    rw [Subgroup.mem_bot, ← hxq]
    exact this
  have hsup : V ⊔ X.map π = (P' : Subgroup (G ⧸ B)) := by
    rw [hP', hV, ← Subgroup.map_sup, hQX]
  obtain ⟨H', hH1, hH2⟩ := (CFSG.Quasithin.gaschutz hV2 P').mpr ⟨X.map π, hle, hinf, hsup⟩
  have hcomm : ∀ g₁ g₂ : G ⧸ B, ⁅g₁, g₂⁆ ∈ H' := by
    intro g₁ g₂
    have h1 : g₁ ∈ V ⊔ H' := by rw [hH2]; trivial
    have h2 : g₂ ∈ V ⊔ H' := by rw [hH2]; trivial
    obtain ⟨v₁, hv₁, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h1
    obtain ⟨v₂, hv₂, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h2
    rw [deq2_commutator_eq_of_central (hVc v₁ hv₁) (hVc v₂ hv₂), commutatorElement_def]
    exact H'.mul_mem (H'.mul_mem (H'.mul_mem ha hb) (H'.inv_mem ha)) (H'.inv_mem hb)
  have hle' : (⊤ : Subgroup (G ⧸ B)) ≤ ⁅(⊤ : Subgroup (G ⧸ B)), ⊤⁆ := by
    have := Subgroup.map_mono (f := π) hperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ] at this
  have hH'top : H' = ⊤ :=
    top_le_iff.mp (hle'.trans (Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => hcomm g₁ g₂))
  rw [hH'top, inf_top_eq] at hH1
  have := (Subgroup.map_eq_bot_iff _).mp hH1
  rwa [QuotientGroup.ker_mk'] at this

end DeqGaschutz

theorem deq2_no_quotient_split {G : Type} [Group G] [Finite G]
    (D Q N : Subgroup G) [D.Normal] [Q.Normal]
    (hDQ : D ≤ Q) (hD : Nat.card D = 8) (hQ : Nat.card Q = 16) (hG : Nat.card G = 2688)
    (hDN : D ≤ N) (hNQ : N ⊓ Q = D) (hN : Nat.card N = 192)
    (hperf : commutator G = ⊤) : False := by
  classical
  have hperf' : (⊤ : Subgroup G) ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
    le_of_eq hperf.symm
  have hQidx : Q.index = 168 := by
    have h := Subgroup.card_mul_index (H := Q)
    rw [hQ, hG] at h
    omega
  have hDQ2 : D.relIndex Q = 2 := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := Q)
    rw [inf_eq_left.mpr hDQ, hD, hQ] at h
    omega
  have hmem : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ D → y ∉ D → x * y⁻¹ ∈ D := by
    intro x hx y hy hxD hyD
    obtain ⟨a, _, hab⟩ := (Subgroup.relIndex_eq_two_iff (H := D) (K := Q)).mp hDQ2
    have hxa : x * a ∈ D := by
      rcases hab x hx with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hxD
    have hya : y * a ∈ D := by
      rcases hab y hy with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hyD
    have := D.mul_mem hxa (D.inv_mem hya)
    convert this using 1
    group
  have hkey : ∀ g : G, ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ D := by
    intro g q hq
    have hx : g * q * g⁻¹ ∈ Q := ‹Q.Normal›.conj_mem q hq g
    by_cases hqD : q ∈ D
    · have hx' : g * q * g⁻¹ ∈ D := ‹D.Normal›.conj_mem q hqD g
      exact D.mul_mem hx' (D.inv_mem hqD)
    · by_cases hxD : g * q * g⁻¹ ∈ D
      · exfalso
        apply hqD
        have := ‹D.Normal›.conj_mem (g * q * g⁻¹) hxD g⁻¹
        convert this using 1
        group
      · exact hmem _ hx q hq hxD hqD
  have hcent : ∀ g : G, ∀ q ∈ Q, QuotientGroup.mk' D g * QuotientGroup.mk' D q =
      QuotientGroup.mk' D q * QuotientGroup.mk' D g := by
    intro g q hq
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := D)).2
    have h := D.inv_mem (hkey g⁻¹ q⁻¹ (Q.inv_mem hq))
    convert h using 1
    group
  have hDN2 : IsPGroup 2 (D.subgroupOf N) := by
    rw [IsPGroup.iff_card]
    refine ⟨3, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv, hD]
    norm_num
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 N))
  have hPD : D.subgroupOf N ≤ (P : Subgroup N) := hDN2.le_sylow_of_normal P
  have hPidx := Subgroup.card_mul_index (H := (P : Subgroup N))
  have hPcard : Nat.card (P : Subgroup N) = 64 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hodd : ¬ 2 ∣ (P : Subgroup N).index := Sylow.not_dvd_index P
    rw [hn, hN] at hPidx
    have hdvd : 2 ^ n ∣ 192 := ⟨_, hPidx.symm⟩
    have hle : 2 ^ n ≤ 192 := Nat.le_of_dvd (by norm_num) hdvd
    have hn7 : n < 8 := by
      by_contra hcon
      push_neg at hcon
      have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hcon
      norm_num at this
      omega
    rw [hn]
    interval_cases n <;> norm_num at hPidx hodd ⊢ <;> omega
  set X : Subgroup G := (P : Subgroup N).map N.subtype with hXdef
  have hXcard : Nat.card X = 64 := by
    rw [hXdef, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hPcard
  have hXN : X ≤ N := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hDX : D ≤ X := by
    intro d hd
    have hmem' : (⟨d, hDN hd⟩ : N) ∈ D.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact hd
    exact Subgroup.mem_map.mpr ⟨⟨d, hDN hd⟩, hPD hmem', rfl⟩
  have hQX : Q ⊓ X = D := by
    apply le_antisymm
    · intro x hx
      have hxN : x ∈ N ⊓ Q := ⟨hXN hx.2, hx.1⟩
      rw [hNQ] at hxN
      exact hxN
    · exact le_inf hDQ hDX
  have hQXD : Nat.card (Q ⊓ X : Subgroup G) = 8 := by rw [hQX, hD]
  have hQXrel : Q.relIndex X = 8 := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := X)
    rw [hQXD, hXcard] at h
    omega
  have hQsup : Q.relIndex (Q ⊔ X) = 8 := by
    rw [Subgroup.relIndex_sup_left, hQXrel]
  have hidx : (Q ⊔ X).index = 21 := by
    have h := Subgroup.relIndex_mul_index (le_sup_left : Q ≤ Q ⊔ X)
    rw [hQsup, hQidx] at h
    omega
  have hQ2 : IsPGroup 2 Q := IsPGroup.iff_card.mpr ⟨4, by rw [hQ]; norm_num⟩
  have hX2 : IsPGroup 2 X := IsPGroup.iff_card.mpr ⟨6, by rw [hXcard]; norm_num⟩
  have hQX2 : IsPGroup 2 (Q ⊔ X : Subgroup G) := IsPGroup.to_sup_of_normal_left hQ2 hX2
  let S : Sylow 2 G := hQX2.toSylow (by rw [hidx]; norm_num)
  have hS : (S : Subgroup G) = Q ⊔ X := rfl
  have hcontra : Q ≤ D :=
    deq2_le_of_central_quotient hDQ hQ2 hcent hperf' S (by rw [hS]; exact le_sup_right)
      hQX.le (by rw [hS])
  have := Subgroup.card_le_of_le hcontra
  omega

variable {G : Type} [Group G] [Finite G]

structure DE2Hyp (Ω : Set (Subgroup G)) : Prop extends DEHyp Ω where
  twin2 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 2

@[expose] def omegaHyp (Ω : Set (Subgroup G)) (H : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ u ∈ H, IsUniqueInvolution L u}

open Classical in
@[expose] noncomputable def flipVal (K : Subgroup G) (q : G) : ZMod 2 :=
  if conjSub q K = K then 0 else 1

section Helpers

variable {Ω : Set (Subgroup G)}

private theorem deq2_twinSet_eq {K J : Subgroup G} (hJ : J ∈ twinSet Ω K) :
    twinSet Ω J = twinSet Ω K := by
  obtain ⟨_, z, hKz, hJz⟩ := hJ
  ext M
  constructor
  · rintro ⟨hM, w, hJw, hMw⟩
    rw [hJw.eq hJz] at hMw
    exact ⟨hM, z, hKz, hMw⟩
  · rintro ⟨hM, w, hKw, hMw⟩
    rw [hKw.eq hKz] at hMw
    exact ⟨hM, z, hJz, hMw⟩

private theorem deq2_twinSet_eq_pair {K J : Subgroup G} (h2 : (twinSet Ω K).ncard = 2)
    (hK : K ∈ twinSet Ω K) (hJ : J ∈ twinSet Ω K) (hne : J ≠ K) :
    twinSet Ω K = {K, J} :=
  (Set.eq_of_subset_of_ncard_le
    (Set.insert_subset hK (Set.singleton_subset_iff.mpr hJ))
    (le_of_eq (by rw [h2, Set.ncard_pair hne.symm]))).symm

private theorem deq2_exists_other {K : Subgroup G} (h2 : (twinSet Ω K).ncard = 2)
    (hK : K ∈ twinSet Ω K) : ∃ J ∈ twinSet Ω K, J ≠ K := by
  obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.mp h2
  rw [hS] at hK ⊢
  rcases hK with rfl | rfl
  · exact ⟨b, by simp, hab.symm⟩
  · exact ⟨a, by simp, hab⟩

private theorem deq2_conjSub_mem_twinSet {L J : Subgroup G} {z x : G}
    (hΩ : ConjInvariant Ω) (hz : IsUniqueInvolution L z) (hxz : x * z = z * x)
    (hJ : J ∈ twinSet Ω L) : conjSub x J ∈ twinSet Ω L := by
  obtain ⟨hJΩ, w, hLw, hJw⟩ := hJ
  have hwz : w = z := hLw.eq hz
  rw [hwz] at hJw
  have hxzx : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  have hc := hJw.conj x
  rw [hxzx] at hc
  exact ⟨hΩ x J hJΩ, z, hz, hc⟩

private theorem deq2_eq_one_or_eq_of_mem_zpowers {z x : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have hk : z ^ k = z ^ (k % (orderOf z : ℤ)) := (zpow_mod_orderOf z k).symm
  rw [hord] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [hk]
    have h0' : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [h0']
    exact zpow_zero z
  · right
    rw [hk]
    have h1' : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [h1']
    exact zpow_one z

private theorem deq2_exists_q8 {L : Subgroup G} {z : G} (hz : IsUniqueInvolution L z)
    (hQ : IsQuatSub L) (hL8 : Nat.card L = 8) : ∃ i j : G, Q8Data L z i j := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ := exists_q8_gen hz hQ hL8
  exact ⟨i, j, ⟨hz, hi, hj, hii, hjj, hji, hNF⟩⟩

private theorem deq2_flipVal_eq_zero_iff {K : Subgroup G} {q : G} :
    flipVal K q = 0 ↔ conjSub q K = K := by
  unfold flipVal
  by_cases hq : conjSub q K = K <;> simp [hq]

private theorem deq2_flipVal_eq_one_iff {K : Subgroup G} {q : G} :
    flipVal K q = 1 ↔ conjSub q K ≠ K := by
  unfold flipVal
  by_cases hq : conjSub q K = K <;> simp [hq]

private theorem deq2_flipVal_cases (K : Subgroup G) (q : G) :
    flipVal K q = 0 ∨ flipVal K q = 1 := by
  unfold flipVal
  by_cases hq : conjSub q K = K <;> simp [hq]

private theorem deq2_flipVal_of_eq {K : Subgroup G} {q q' : G}
    (h : conjSub q K = conjSub q' K) : flipVal K q = flipVal K q' := by
  unfold flipVal
  rw [h]

private theorem deq2_conjSub_conj (g q : G) (K : Subgroup G) :
    conjSub (g * q * g⁻¹) (conjSub g K) = conjSub g (conjSub q K) := by
  rw [conjSub_mul, conjSub_mul, conjSub_inv_conjSub]

private theorem deq2_mul_eq_one_iff {z a b : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) : b * a = 1 ↔ b = a := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · simp
  · simp [hz1]
  · simp [hz1, hz1.symm]
  · simp [hz2]

private theorem deq2_dComm_involution_one {L : Subgroup G} {z : G}
    (hz : IsUniqueInvolution L z) {w : G} (hw : w ∈ L) : dComm z w = 1 := by
  have hc := conj_of_mem_mem hz hw (Or.inr rfl)
  exact dComm_eq_one_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc).symm

private theorem deq2_seven_orbit {α : Type} [MulAction G α] [Finite α] (hα : Nat.card α = 8)
    {g : G} (hg : orderOf g = 7) {x₁ : α} (hfix : ∀ y : α, g • y = y → y = x₁)
    (hx₁ : g • x₁ = x₁) {z y : α} (hz : z ≠ x₁) (hy : y ≠ x₁) :
    ∃ k : ℕ, (g ^ k) • z = y := by
  classical
  haveI := Fintype.ofFinite α
  have hg7 : g ^ 7 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hpowmod : ∀ k : ℕ, g ^ k = g ^ (k % 7) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 7, pow_add, pow_mul, hg7, one_pow, one_mul]
  have hstab : ∀ k : ℕ, (g ^ k) • x₁ = x₁ := fun k =>
    MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer G x₁).pow_mem (MulAction.mem_stabilizer_iff.mpr hx₁) k)
  have htrick : ∀ m : ℕ, 0 < m → m < 7 → ∀ w : α, (g ^ m) • w = w → g • w = w := by
    intro m hm0 hm7 w hw
    have hpow : (g ^ m) ^ (m ^ 5) • w = w := by
      have hmem : g ^ m ∈ MulAction.stabilizer G w := MulAction.mem_stabilizer_iff.mpr hw
      exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G w).pow_mem hmem _)
    have hgm : (g ^ m) ^ (m ^ 5) = g := by
      rw [← pow_mul, hpowmod, show m * m ^ 5 % 7 = 1 by interval_cases m <;> norm_num, pow_one]
    rwa [hgm] at hpow
  have hkey : ∀ a b : ℕ, a < b → b < 7 → (g ^ a) • z = (g ^ b) • z → False := by
    intro a b hab hb hab'
    have hc : (g ^ (b - a)) • z = z := by
      have e : g ^ b = g ^ a * g ^ (b - a) := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le]
      rw [e, mul_smul] at hab'
      exact (smul_left_cancel (g ^ a) hab').symm
    have hfixz : g • z = z := htrick (b - a) (Nat.sub_pos_of_lt hab) (by omega) z hc
    exact hz (hfix z hfixz)
  have hinj : ∀ i j : ℕ, i < 7 → j < 7 → (g ^ i) • z = (g ^ j) • z → i = j := by
    intro i j hi hj hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (hkey i j hlt hj hij).elim
    · exact heq
    · exact (hkey j i hgt hi hij.symm).elim
  have hTcard : (Finset.univ.erase x₁).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x₁), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hα]
  have hSsub : (Finset.range 7).image (fun k : ℕ => (g ^ k) • z) ⊆ Finset.univ.erase x₁ := by
    intro w hw
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_erase]
    refine ⟨fun hx => hz ?_, Finset.mem_univ _⟩
    calc z = (g ^ k)⁻¹ • ((g ^ k) • z) := (inv_smul_smul _ _).symm
      _ = (g ^ k)⁻¹ • x₁ := by rw [hx]
      _ = x₁ := by
        have hinv : (g ^ k)⁻¹ ∈ MulAction.stabilizer G x₁ :=
          (MulAction.stabilizer G x₁).inv_mem (MulAction.mem_stabilizer_iff.mpr (hstab k))
        exact MulAction.mem_stabilizer_iff.mp hinv
  have hScard : ((Finset.range 7).image (fun k : ℕ => (g ^ k) • z)).card = 7 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact hinj i j hi hj hij
  have hST : (Finset.range 7).image (fun k : ℕ => (g ^ k) • z) = Finset.univ.erase x₁ :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard, hTcard])
  have hymem : y ∈ Finset.univ.erase x₁ := Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩
  rw [← hST] at hymem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hymem
  exact ⟨k, hk⟩

private theorem deq2_zmod_three : ∀ a b c : ZMod 2, (a = 0 → b = 0 → c = 0) →
    (b = 0 → c = 0 → a = 0) → (a = 0 → c = 0 → b = 0) → c ≠ a + b → a = 1 ∧ b = 1 ∧ c = 1 := by
  decide

private theorem deq2_zmod_const : ∀ a b c : ZMod 2, (a = 0 → b = 0 → c = 0) →
    (b = 0 → c = 0 → a = 0) → (a = 0 → c = 0 → b = 0) →
    (a + 1 = 0 → b + 1 = 0 → c + 1 = 0) → (b + 1 = 0 → c + 1 = 0 → a + 1 = 0) →
    (a + 1 = 0 → c + 1 = 0 → b + 1 = 0) → a = b ∧ b = c := by
  decide

end Helpers

namespace DE2Hyp

variable {Ω : Set (Subgroup G)} (h : DE2Hyp Ω)
include h

private theorem deq2_involution_mem {L : Subgroup G} {z : G} (hL : L ∈ Ω)
    (hz : IsUniqueInvolution L z) : z ∈ zGroup Ω :=
  h.mem_zGroup_iff.mpr (Or.inr ⟨L, hL, hz⟩)

private theorem deq2_eq_one_of_odd_mem_centralizer {x : G}
    (hx : x ∈ Subgroup.centralizer (zGroup Ω : Set G)) {m : ℕ} (hxp : x ^ (2 * m + 1) = 1) :
    x = 1 := by
  have hnorm : ∀ L ∈ Ω, x ∈ Subgroup.normalizer (L : Set G) := by
    intro L hL
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    have hxz : x * z = z * x :=
      (Subgroup.mem_centralizer_iff.mp hx z (deq2_involution_mem h hL hz)).symm
    rw [mem_normalizer_iff_conjSub_eq]
    by_contra hne
    have hself : L ∈ twinSet Ω L := ⟨hL, z, hz, hz⟩
    have hLmem : conjSub x L ∈ twinSet Ω L :=
      deq2_conjSub_mem_twinSet h.hyp.conjInvariant hz hxz hself
    have hpair := deq2_twinSet_eq_pair (h.twin2 L hL) hself hLmem hne
    have hx' := deq2_conjSub_mem_twinSet h.hyp.conjInvariant hz hxz hLmem
    rw [hpair] at hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    have hLL : conjSub x (conjSub x L) = L := by
      rcases hx' with h1 | h1
      · exact h1
      · exact absurd (conjSub_injective x h1) hne
    have hsq : conjSub (x * x) L = L := by
      rw [conjSub_mul]
      exact hLL
    have hpowsq : ∀ n : ℕ, conjSub ((x * x) ^ n) L = L := by
      intro n
      induction n with
      | zero => rw [pow_zero, conjSub_one]
      | succ k ih => rw [pow_succ, conjSub_mul, hsq, ih]
    have hodd : conjSub (x ^ (2 * m + 1)) L = conjSub x L := by
      rw [show x ^ (2 * m + 1) = x * (x * x) ^ m by rw [pow_succ', pow_mul, pow_two],
        conjSub_mul, hpowsq m]
    rw [hxp, conjSub_one] at hodd
    exact hne hodd.symm
  have hmem : ∀ L ∈ Ω, ∀ y ∈ L, Commute x y := by
    intro L hL y hy
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    have hxz : x * z = z * x :=
      (Subgroup.mem_centralizer_iff.mp hx z (deq2_involution_mem h hL hz)).symm
    have hnL : x ∈ Subgroup.normalizer (L : Set G) := hnorm L hL
    obtain ⟨i, j, hQ⟩ := deq2_exists_q8 hz (h.isQuatSub_of_mem hL) (h.card L hL)
    have hcomm : ∀ w ∈ L, dComm x w = 1 ∨ dComm x w = z := by
      intro w hw
      have hC : dComm x w ∈ L ⊓ Subgroup.centralizer (zGroup Ω : Set G) := by
        refine ⟨dComm_mem hnL hw, ?_⟩
        have e : dComm x w = x * (w * x⁻¹ * w⁻¹) := by unfold dComm; group
        rw [e]
        exact (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hx
          (h.centralizer_zGroup_normal.conj_mem x⁻¹
            ((Subgroup.centralizer (zGroup Ω : Set G)).inv_mem hx) w)
      rw [h.inf_centralizer_zGroup hL hz] at hC
      exact deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one hC
    have hcz : Commute (x ^ 2) z := (show Commute x z from hxz).pow_left 2
    have hci : Commute (x ^ 2) i := commute_sq_of_dComm hz hxz (hcomm i hQ.mem_i) rfl
    have hcj : Commute (x ^ 2) j := commute_sq_of_dComm hz hxz (hcomm j hQ.mem_j) rfl
    have hsq2 : Commute (x ^ 2) y := commute_sq_of_gen hQ hcz hci hcj hy
    have hpow : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hxp, one_mul]
    have hxy := hsq2.pow_left (m + 1)
    rw [hpow] at hxy
    exact hxy
  have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← h.gen]
    apply pSpan_le
    intro L hL y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hmem L hL y hy).eq.symm
  have hxcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent (Subgroup.mem_top g))
  rw [h.center, Subgroup.mem_bot] at hxcenter
  exact hxcenter

private theorem deq2_isPGroup_centralizer :
    IsPGroup 2 (Subgroup.centralizer (zGroup Ω : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd
      (Nat.card (Subgroup.centralizer (zGroup Ω : Set G))) with hpow | ⟨p, hp, hdvd, hodd⟩
  · exact hpow
  · exfalso
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hord : orderOf (c : G) = p := (Subgroup.orderOf_coe c).trans hc
    obtain ⟨m, hm⟩ := hodd
    have hxp : (c : G) ^ (2 * m + 1) = 1 := by
      rw [← hm, ← hord, pow_orderOf_eq_one]
    have hx1 := deq2_eq_one_of_odd_mem_centralizer h c.2 hxp
    rw [hx1, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm

theorem centralizer_zGroup_eq_pCore :
    Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨h.centralizer_zGroup_normal, h.deq2_isPGroup_centralizer⟩
  · exact h.pCore_le_centralizer_zGroup

theorem ncard_eq_fourteen : Ω.ncard = 14 := by
  obtain ⟨L, hL, -⟩ := h.exists_ne
  rw [h.ncard_eq_seven_mul hL, h.twin2 L hL]

theorem conjSub_mem_twinSet {q : G} (hq : q ∈ pCore 2 G) {K : Subgroup G} (hK : K ∈ Ω) :
    conjSub q K ∈ twinSet Ω K := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  have hqC : q ∈ Subgroup.centralizer (zGroup Ω : Set G) := h.pCore_le_centralizer_zGroup hq
  have hxz : q * z = z * q :=
    (Subgroup.mem_centralizer_iff.mp hqC z (deq2_involution_mem h hK hz)).symm
  exact deq2_conjSub_mem_twinSet h.hyp.conjInvariant hz hxz ⟨hK, z, hz, hz⟩

theorem flipVal_eq_of_mem_twinSet {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ twinSet Ω K)
    {q : G} (hq : q ∈ pCore 2 G) : flipVal J q = flipVal K q := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  by_cases hJK : J = K
  · rw [hJK]
  have hJΩ : J ∈ Ω := hJ.1
  have hKS : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hS : twinSet Ω K = {K, J} := deq2_twinSet_eq_pair (h.twin2 K hK) hKS hJ hJK
  have hJS : twinSet Ω J = twinSet Ω K := deq2_twinSet_eq hJ
  have h1 : conjSub q K ∈ twinSet Ω K := h.conjSub_mem_twinSet hq hK
  have h2 : conjSub q J ∈ twinSet Ω K := by
    rw [← hJS]
    exact h.conjSub_mem_twinSet hq hJΩ
  rw [hS] at h1 h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  by_cases hqK : conjSub q K = K
  · have hqJ : conjSub q J = J := by
      rcases h2 with h2 | h2
      · exact absurd (conjSub_injective q (h2.trans hqK.symm)) hJK
      · exact h2
    rw [deq2_flipVal_eq_zero_iff.mpr hqJ, deq2_flipVal_eq_zero_iff.mpr hqK]
  · have hKJ : conjSub q K = J := h1.resolve_left hqK
    have hqJ : conjSub q J ≠ J := by
      intro hqJ
      exact hJK (conjSub_injective q (hKJ.trans hqJ.symm)).symm
    rw [deq2_flipVal_eq_one_iff.mpr hqJ, deq2_flipVal_eq_one_iff.mpr hqK]

theorem flipVal_mul {K : Subgroup G} (hK : K ∈ Ω) {q q' : G} (hq : q ∈ pCore 2 G)
    (hq' : q' ∈ pCore 2 G) : flipVal K (q * q') = flipVal K q + flipVal K q' := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  have hKS : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have h2 := h.twin2 K hK
  by_cases hq'K : conjSub q' K = K
  · have e : flipVal K (q * q') = flipVal K q :=
      deq2_flipVal_of_eq (by rw [conjSub_mul, hq'K])
    rw [e, deq2_flipVal_eq_zero_iff.mpr hq'K, add_zero]
  · have hJ : conjSub q' K ∈ twinSet Ω K := h.conjSub_mem_twinSet hq' hK
    have hS : twinSet Ω K = {K, conjSub q' K} :=
      deq2_twinSet_eq_pair h2 hKS hJ hq'K
    have hJne : conjSub q' K ≠ K := hq'K
    have hJs : conjSub (q * q') K = conjSub q (conjSub q' K) := conjSub_mul q q' K
    rw [deq2_flipVal_eq_one_iff.mpr hq'K]
    rcases deq2_flipVal_cases K q with hqz | hqo
    · rw [hqz, zero_add]
      have hsub := h.flipVal_eq_of_mem_twinSet hK hJ hq
      have hqJ : conjSub q (conjSub q' K) = conjSub q' K :=
        deq2_flipVal_eq_zero_iff.mp (hsub.trans hqz)
      exact deq2_flipVal_eq_one_iff.mpr (by rw [hJs, hqJ]; exact hJne)
    · have hqK : conjSub q K = conjSub q' K := by
        have h1 := h.conjSub_mem_twinSet hq hK
        rw [hS] at h1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
        exact h1.resolve_left (deq2_flipVal_eq_one_iff.mp hqo)
      have hqJK : conjSub q (conjSub q' K) = K := by
        have h3 : conjSub q (conjSub q' K) ∈ twinSet Ω K := by
          rw [← deq2_twinSet_eq hJ]
          exact h.conjSub_mem_twinSet hq hJ.1
        rw [hS] at h3
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
        rcases h3 with h3 | h3
        · exact h3
        · exact absurd (conjSub_injective q (hqK.trans h3.symm)) (Ne.symm hJne)
      rw [hqo]
      have e0 : flipVal K (q * q') = 0 :=
        deq2_flipVal_eq_zero_iff.mpr (by rw [hJs, hqJK])
      rw [e0]
      decide

theorem flipVal_conj {K : Subgroup G} (hK : K ∈ Ω) (g : G) {q : G} (hq : q ∈ pCore 2 G) :
    flipVal (conjSub g K) (g * q * g⁻¹) = flipVal K q := by
  by_cases hqK : conjSub q K = K
  · rw [deq2_flipVal_eq_zero_iff.mpr hqK]
    apply deq2_flipVal_eq_zero_iff.mpr
    rw [deq2_conjSub_conj, hqK]
  · rw [deq2_flipVal_eq_one_iff.mpr hqK]
    apply deq2_flipVal_eq_one_iff.mpr
    rw [deq2_conjSub_conj]
    intro hc
    exact hqK (conjSub_injective g hc)

theorem exists_flip {K : Subgroup G} (hK : K ∈ Ω) : ∃ q ∈ pCore 2 G, flipVal K q = 1 := by
  obtain ⟨u, hu⟩ := h.exists_isUniqueInvolution hK
  have hKS : K ∈ twinSet Ω K := ⟨hK, u, hu, hu⟩
  obtain ⟨J, hJ, hJne⟩ := deq2_exists_other (h.twin2 K hK) hKS
  obtain ⟨g, hgC, hgJ⟩ := h.exists_swap_of_mem_twinSet hK hJ hu
  rw [h.centralizer_eq_sup hK hu] at hgC
  haveI : (Subgroup.centralizer (zGroup Ω : Set G)).Normal := h.centralizer_zGroup_normal
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_right.mp hgC
  have hcp : c ∈ pCore 2 G := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact hc
  refine ⟨c, hcp, deq2_flipVal_eq_one_iff.mpr ?_⟩
  intro hcK
  apply hJne
  rw [← hgJ, ← hnc, conjSub_mul, hcK]
  exact mem_normalizer_iff_conjSub_eq.mp hn

private theorem deq2_dComm_pCore_mem {f : G} (hf : f ∈ pCore 2 G) {L : Subgroup G} (hL : L ∈ Ω)
    (hfL : flipVal L f = 0) {z : G} (hz : IsUniqueInvolution L z) {w : G} (hw : w ∈ L) :
    dComm f w ∈ Subgroup.zpowers z := by
  have hnf : f ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (deq2_flipVal_eq_zero_iff.mp hfL)
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  have hmemQ : dComm f w ∈ pCore 2 G := by
    have e : dComm f w = f * (w * f⁻¹ * w⁻¹) := by unfold dComm; group
    rw [e]
    exact (pCore 2 G).mul_mem hf (hQn.conj_mem f⁻¹ ((pCore 2 G).inv_mem hf) w)
  have hmemL : dComm f w ∈ L := dComm_mem hnf hw
  have hI : dComm f w ∈ L ⊓ pCore 2 G := ⟨hmemL, hmemQ⟩
  rw [h.inf_pCore hL hz] at hI
  exact hI

theorem exists_conj_eq_mul_zGroup {f : G} (hf : f ∈ pCore 2 G) (hfN : ∀ L ∈ Ω, flipVal L f = 0)
    (g : G) : ∃ d ∈ zGroup Ω, g * f * g⁻¹ = f * d := by
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  let T : Subgroup G :=
    { carrier := {x : G | ∃ d ∈ zGroup Ω, x * f * x⁻¹ = f * d}
      mul_mem' := by
        rintro a b ⟨d, hd, ha⟩ ⟨d', hd', hb⟩
        refine ⟨d * (a * d' * a⁻¹), (zGroup Ω).mul_mem hd
          (h.zGroup_normal.conj_mem d' hd' a), ?_⟩
        calc a * b * f * (a * b)⁻¹ = a * (b * f * b⁻¹) * a⁻¹ := by group
          _ = a * (f * d') * a⁻¹ := by rw [hb]
          _ = (a * f * a⁻¹) * (a * d' * a⁻¹) := by group
          _ = f * d * (a * d' * a⁻¹) := by rw [ha]
          _ = f * (d * (a * d' * a⁻¹)) := by group
      one_mem' := ⟨1, (zGroup Ω).one_mem, by group⟩
      inv_mem' := by
        rintro a ⟨d, hd, ha⟩
        have hdD : a⁻¹ * d⁻¹ * a ∈ zGroup Ω := by
          have := h.zGroup_normal.conj_mem d⁻¹ ((zGroup Ω).inv_mem hd) a⁻¹
          rwa [inv_inv] at this
        refine ⟨a⁻¹ * d⁻¹ * a, hdD, ?_⟩
        have e1 : a * f = f * d * a := by
          rw [← ha]
          group
        have e2 : a⁻¹ * f = f * a⁻¹ * d⁻¹ := by
          calc a⁻¹ * f = a⁻¹ * f * d * a * a⁻¹ * d⁻¹ := by group
            _ = a⁻¹ * (f * d * a) * a⁻¹ * d⁻¹ := by group
            _ = a⁻¹ * (a * f) * a⁻¹ * d⁻¹ := by rw [← e1]
            _ = f * a⁻¹ * d⁻¹ := by group
        rw [inv_inv, e2]
        group }
  have hT : (⊤ : Subgroup G) ≤ T := by
    rw [← h.gen]
    apply pSpan_le
    intro L hL w hw
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    have hdw := deq2_dComm_pCore_mem h hf hL (hfN L hL) hz hw
    have hzD : Subgroup.zpowers z ≤ zGroup Ω :=
      Subgroup.zpowers_le.mpr (deq2_involution_mem h hL hz)
    have hx : (dComm f w)⁻¹ ∈ zGroup Ω := hzD ((Subgroup.zpowers z).inv_mem hdw)
    refine ⟨f⁻¹ * (dComm f w)⁻¹ * f, ?_, ?_⟩
    · have := h.zGroup_normal.conj_mem _ hx f⁻¹
      rwa [inv_inv] at this
    · unfold dComm
      group
  exact hT (Subgroup.mem_top g)

theorem ncard_centralized_coset {f : G} (hf : f ∈ pCore 2 G) (hfN : ∀ L ∈ Ω, flipVal L f = 0)
    {L : Subgroup G} (hL : L ∈ Ω) :
    {d : G | d ∈ zGroup Ω ∧ ∀ y ∈ L, (f * d) * y = y * (f * d)}.ncard = 2 := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
  have hfL : flipVal L f = 0 := hfN L hL
  have hnf : f ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (deq2_flipVal_eq_zero_iff.mp hfL)
  have hzL : z ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hz.mem
  have hfc : ∀ w ∈ L, dComm f w = 1 ∨ dComm f w = z := fun w hw =>
    deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (deq2_dComm_pCore_mem h hf hL hfL hz hw)
  let φ : L →* Subgroup.zpowers z :=
    { toFun := fun w => ⟨dComm f (w : G), deq2_dComm_pCore_mem h hf hL hfL hz w.2⟩
      map_one' := Subtype.ext (by simp [dComm])
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        exact dComm_mul_right hz x.2 y.2 hnf (hfc y y.2)) }
  have hφz : φ ⟨z, hz.mem⟩ = 1 := Subtype.ext (dComm_z hz hnf)
  obtain ⟨d₀, hd₀, hd₀φ⟩ := h.exists_dComm_eq_hom hL hz φ hφz
  have hkey : ∀ d ∈ zGroup Ω, ((∀ y ∈ L, (f * d) * y = y * (f * d)) ↔
      ∀ w ∈ L, dComm d w = dComm f w) := by
    intro d hd
    constructor
    · intro hc w hw
      have hcw := hc w hw
      rw [← dComm_eq_one_iff, dComm_mul_left hz hnf
        (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hL hz hd hw))]
        at hcw
      exact (deq2_mul_eq_one_iff hz.sq hz.ne_one (hfc w hw)
        (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hL hz hd hw))).mp
        hcw
    · intro hc y hy
      rw [← dComm_eq_one_iff, dComm_mul_left hz hnf
        (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hL hz hd hy))]
      exact (deq2_mul_eq_one_iff hz.sq hz.ne_one (hfc y hy)
        (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hL hz hd hy))).mpr
        (hc y hy)
  have hS : {d : G | d ∈ zGroup Ω ∧ ∀ y ∈ L, (f * d) * y = y * (f * d)} = {d₀, z * d₀} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hd, hc⟩
      have hP := (hkey d hd).mp hc
      have hdd : ∀ k ∈ L, dComm d k = dComm d₀ k := fun k hk =>
        (hP k hk).trans (hd₀φ ⟨k, hk⟩).symm
      have hm := h.eq_of_dComm_eq hL hz hd hd₀ hdd
      rcases deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one hm with h1 | h1
      · left
        exact (mul_inv_eq_one.mp h1).symm
      · right
        rw [mul_inv_eq_iff_eq_mul.mp h1, ← mul_assoc, hz.sq, one_mul]
    · rintro (h1 | h1)
      · rw [h1]
        refine ⟨hd₀, (hkey d₀ hd₀).mpr ?_⟩
        intro w hw
        exact hd₀φ ⟨w, hw⟩
      · have hzd : z * d₀ ∈ zGroup Ω := (zGroup Ω).mul_mem (deq2_involution_mem h hL hz) hd₀
        rw [h1]
        refine ⟨hzd, (hkey (z * d₀) hzd).mpr ?_⟩
        intro w hw
        rw [dComm_mul_left hz hzL
          (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hL hz hd₀ hw)),
          deq2_dComm_involution_one hz hw, mul_one]
        exact hd₀φ ⟨w, hw⟩
  have hne : d₀ ≠ z * d₀ := by
    intro heq
    apply hz.ne_one
    simpa using heq
  rw [hS]
  exact Set.ncard_pair hne

private theorem deq2_index_centralizer {L : Subgroup G} {u : G} (hL : L ∈ Ω)
    (hu : IsUniqueInvolution L u) : (Subgroup.centralizer ({u} : Set G)).index = 7 := by
  have huD : u ∈ zGroup Ω := deq2_involution_mem h hL hu
  have hset : conjugatesOf u = (fun x : zGroup Ω => (x : G)) '' {x : zGroup Ω | x ≠ 1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hxD : x ∈ zGroup Ω := by
        rw [← hc]
        exact h.zGroup_normal.conj_mem u huD c
      have hx1 : x ≠ 1 := by
        rw [← hc]
        intro h1
        apply hu.ne_one
        calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
          _ = 1 := by rw [h1]; group
      exact ⟨⟨x, hxD⟩, fun h1 => hx1 (congrArg Subtype.val h1), rfl⟩
    · rintro ⟨⟨y, hyD⟩, hy1, rfl⟩
      have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
      obtain ⟨L', hL', hy⟩ : ∃ L' ∈ Ω, IsUniqueInvolution L' y := by
        rcases h.mem_zGroup_iff.mp hyD with h1 | h1
        · exact absurd h1 hy1'
        · exact h1
      obtain ⟨g, hg⟩ := h.exists_conj_involution hL hL' hu hy
      exact isConj_iff.mpr ⟨g, hg⟩
  rw [Subgroup.index_centralizer_eq_ncard, hset,
    Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  exact h.card_zGroup_ne_one

private theorem deq2_fixed_free {g : G} (hg7 : orderOf g = 7) {δ : G} (hδ : δ ∈ zGroup Ω)
    (hfix : g * δ * g⁻¹ = δ) : δ = 1 := by
  by_contra hδ1
  obtain ⟨L, hL, hu⟩ : ∃ L ∈ Ω, IsUniqueInvolution L δ := by
    rcases h.mem_zGroup_iff.mp hδ with h1 | h1
    · exact absurd h1 hδ1
    · exact h1
  have hgC : g ∈ Subgroup.centralizer ({δ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have hsub : Subgroup.centralizer (zGroup Ω : Set G) ≤ Subgroup.centralizer ({δ} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hx δ hδ).symm
  have hrel := Subgroup.relIndex_mul_index hsub
  rw [deq2_index_centralizer h hL hu, h.index_centralizer_zGroup] at hrel
  have h24 : (Subgroup.centralizer (zGroup Ω : Set G)).relIndex
      (Subgroup.centralizer ({δ} : Set G)) = 24 := by omega
  set H := Subgroup.centralizer (zGroup Ω : Set G) with hH
  set K := Subgroup.centralizer ({δ} : Set G) with hK
  haveI : H.Normal := h.centralizer_zGroup_normal
  let x : K := ⟨g, hgC⟩
  have hx7 : x ^ 7 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hg7]
    exact pow_orderOf_eq_one g
  have hord7 : orderOf (QuotientGroup.mk' (H.subgroupOf K) x) ∣ 7 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hx7, map_one]
  have hord24 : orderOf (QuotientGroup.mk' (H.subgroupOf K) x) ∣ 24 := by
    have := orderOf_dvd_natCard (QuotientGroup.mk' (H.subgroupOf K) x)
    rw [← Subgroup.index, ← Subgroup.relIndex, h24] at this
    exact this
  have hone : orderOf (QuotientGroup.mk' (H.subgroupOf K) x) = 1 := by
    have hg1 : orderOf (QuotientGroup.mk' (H.subgroupOf K) x) ∣ Nat.gcd 7 24 :=
      Nat.dvd_gcd hord7 hord24
    rw [show Nat.gcd 7 24 = 1 by norm_num] at hg1
    exact Nat.dvd_one.mp hg1
  have hxH : x ∈ H.subgroupOf K := by
    rw [← QuotientGroup.eq_one_iff]
    exact orderOf_eq_one_iff.mp hone
  have hgH : g ∈ H := Subgroup.mem_subgroupOf.mp hxH
  obtain ⟨k, hk⟩ := h.deq2_isPGroup_centralizer ⟨g, hgH⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h7 : 7 ∣ 2 ^ k := by
    rw [← hg7]
    exact orderOf_dvd_of_pow_eq_one hk'
  have := (Nat.prime_seven.dvd_of_dvd_pow h7)
  norm_num at this

private theorem deq2_exists_order_seven : ∃ g : G, orderOf g = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply exists_prime_orderOf_dvd_card' 7
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer (zGroup Ω : Set G))
  rw [h.index_centralizer_zGroup] at h1
  rw [← h1]
  exact Dvd.dvd.mul_left (by norm_num) _

theorem exists_conj_coset_eq {f : G} (hf : f ∈ pCore 2 G) (hfN : ∀ L ∈ Ω, flipVal L f = 0)
    (hfD : f ∉ zGroup Ω) {d d' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω) :
    ∃ g : G, g * (f * d) * g⁻¹ = f * d' := by
  classical
  obtain ⟨g₇, hg₇⟩ := h.deq2_exists_order_seven
  obtain ⟨X, hXdef⟩ : ∃ X : Set G, X = {x | ∃ e ∈ zGroup Ω, x = f * e} := ⟨_, rfl⟩
  have hmemX : ∀ x, x ∈ X ↔ ∃ e ∈ zGroup Ω, x = f * e := fun x => by rw [hXdef]; rfl
  have hXc : ∀ g : G, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g x hx
    obtain ⟨e, he, rfl⟩ := (hmemX x).mp hx
    obtain ⟨c, hc, hgc⟩ := h.exists_conj_eq_mul_zGroup hf hfN g
    refine (hmemX _).mpr ⟨c * (g * e * g⁻¹), (zGroup Ω).mul_mem hc
      (h.zGroup_normal.conj_mem e he g), ?_⟩
    calc g * (f * e) * g⁻¹ = (g * f * g⁻¹) * (g * e * g⁻¹) := by group
      _ = f * c * (g * e * g⁻¹) := by rw [hgc]
      _ = f * (c * (g * e * g⁻¹)) := by group
  letI act : MulAction G X :=
    { smul := fun g x => ⟨g * x * g⁻¹, hXc g x x.2⟩
      one_smul := fun x => Subtype.ext (by show (1 : G) * x.1 * (1 : G)⁻¹ = x.1; group)
      mul_smul := fun a b x => Subtype.ext (by
        show (a * b) * x.1 * (a * b)⁻¹ = a * (b * x.1 * b⁻¹) * a⁻¹
        group) }
  have hsmul : ∀ (g : G) (y : X), g • y = ⟨g * y.1 * g⁻¹, hXc g y.1 y.2⟩ := fun _ _ => rfl
  have hXcard : Nat.card X = 8 := by
    have e : zGroup Ω ≃ X :=
      Equiv.ofBijective (fun e => (⟨f * e.1, (hmemX _).mpr ⟨e.1, e.2, rfl⟩⟩ : X))
        ⟨fun a b hab => Subtype.ext (mul_left_cancel (congrArg Subtype.val hab)),
          fun x => by
            obtain ⟨e, he, hx⟩ := (hmemX x.1).mp x.2
            exact ⟨⟨e, he⟩, Subtype.ext hx.symm⟩⟩
    rw [← Nat.card_congr e, h.card_zGroup]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hH7 : IsPGroup 7 (Subgroup.zpowers g₇) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hg₇, pow_one]⟩
  have hcong := hH7.card_modEq_card_fixedPoints X
  have hfixmem : ∀ y : X, y ∈ MulAction.fixedPoints (Subgroup.zpowers g₇) X ↔
      g₇ * y.1 * g₇⁻¹ = y.1 := by
    intro y
    constructor
    · intro hy
      have h1 := MulAction.mem_fixedPoints.mp hy ⟨g₇, Subgroup.mem_zpowers g₇⟩
      exact congrArg Subtype.val h1
    · intro hy
      rw [MulAction.mem_fixedPoints]
      rintro ⟨m, hm⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hgC : g₇ ∈ Subgroup.centralizer ({y.1} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hy)
      have hmC := (Subgroup.centralizer ({y.1} : Set G)).zpow_mem hgC k
      apply Subtype.ext
      show m * y.1 * m⁻¹ = y.1
      rw [← hk]
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hmC)
  have huniq : ∀ y z : X, g₇ * y.1 * g₇⁻¹ = y.1 → g₇ * z.1 * g₇⁻¹ = z.1 → y = z := by
    intro y z hy hz
    obtain ⟨e, he, hye⟩ := (hmemX y.1).mp y.2
    obtain ⟨e', he', hze⟩ := (hmemX z.1).mp z.2
    have hδD : y.1⁻¹ * z.1 ∈ zGroup Ω := by
      rw [hye, hze, show (f * e)⁻¹ * (f * e') = e⁻¹ * e' by group]
      exact (zGroup Ω).mul_mem ((zGroup Ω).inv_mem he) he'
    have hy' : g₇ * y.1⁻¹ * g₇⁻¹ = y.1⁻¹ := by
      calc g₇ * y.1⁻¹ * g₇⁻¹ = (g₇ * y.1 * g₇⁻¹)⁻¹ := by group
        _ = y.1⁻¹ := by rw [hy]
    have hδfix : g₇ * (y.1⁻¹ * z.1) * g₇⁻¹ = y.1⁻¹ * z.1 := by
      calc g₇ * (y.1⁻¹ * z.1) * g₇⁻¹ = (g₇ * y.1⁻¹ * g₇⁻¹) * (g₇ * z.1 * g₇⁻¹) := by group
        _ = y.1⁻¹ * z.1 := by rw [hy', hz]
    have h1 := h.deq2_fixed_free hg₇ hδD hδfix
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hfixcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g₇) X) = 1 := by
    have hsub : Subsingleton (MulAction.fixedPoints (Subgroup.zpowers g₇) X) :=
      ⟨fun a b => Subtype.ext (huniq a.1 b.1 ((hfixmem a.1).mp a.2) ((hfixmem b.1).mp b.2))⟩
    have hle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g₇) X) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr hsub
    have hmod := hcong
    rw [hXcard] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨⟨x₁, hx₁fix⟩, hall⟩ := Nat.card_eq_one_iff_exists.mp hfixcard
  have hx₁ : g₇ * x₁.1 * g₇⁻¹ = x₁.1 := (hfixmem x₁).mp hx₁fix
  have hfixu : ∀ y : X, g₇ • y = y → y = x₁ := by
    intro y hy
    have hy' : g₇ * y.1 * g₇⁻¹ = y.1 := congrArg Subtype.val hy
    exact congrArg Subtype.val (hall ⟨y, (hfixmem y).mpr hy'⟩)
  have hx₁g : g₇ • x₁ = x₁ := Subtype.ext hx₁
  have hnotfix : ∃ g : G, g * x₁.1 * g⁻¹ ≠ x₁.1 := by
    by_contra hcon
    push_neg at hcon
    have hc : x₁.1 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact mul_inv_eq_iff_eq_mul.mp (hcon g)
    rw [h.center, Subgroup.mem_bot] at hc
    obtain ⟨e, he, hxe⟩ := (hmemX x₁.1).mp x₁.2
    apply hfD
    have hfe : f = e⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hxe, hc])
    rw [hfe]
    exact (zGroup Ω).inv_mem he
  obtain ⟨g', hg'⟩ := hnotfix
  have hz₀ne : g' • x₁ ≠ x₁ := fun h1 => hg' (congrArg Subtype.val h1)
  have hreach : ∀ y : X, ∃ a : G, a • x₁ = y := by
    intro y
    by_cases hy : y = x₁
    · exact ⟨1, by rw [one_smul, hy]⟩
    · obtain ⟨k, hk⟩ := deq2_seven_orbit hXcard hg₇ hfixu hx₁g hz₀ne hy
      exact ⟨g₇ ^ k * g', by rw [mul_smul, hk]⟩
  obtain ⟨a, ha⟩ := hreach ⟨f * d, (hmemX _).mpr ⟨d, hd, rfl⟩⟩
  obtain ⟨b, hb⟩ := hreach ⟨f * d', (hmemX _).mpr ⟨d', hd', rfl⟩⟩
  have hA : a * x₁.1 * a⁻¹ = f * d := congrArg Subtype.val ha
  have hB : b * x₁.1 * b⁻¹ = f * d' := congrArg Subtype.val hb
  refine ⟨b * a⁻¹, ?_⟩
  rw [← hA, ← hB]
  group

theorem mem_zGroup_of_flipVal_eq_zero {q : G} (hq : q ∈ pCore 2 G)
    (hq0 : ∀ L ∈ Ω, flipVal L q = 0) : q ∈ zGroup Ω := by
  classical
  by_contra hqD
  obtain ⟨X, hXdef⟩ : ∃ X : Set G, X = {x | ∃ e ∈ zGroup Ω, x = q * e} := ⟨_, rfl⟩
  have hmemX : ∀ x, x ∈ X ↔ ∃ e ∈ zGroup Ω, x = q * e := fun x => by rw [hXdef]; rfl
  obtain ⟨r, hr⟩ : ∃ r : G → Subgroup G → Prop,
      ∀ x L, r x L ↔ ∀ y ∈ L, x * y = y * x := ⟨_, fun _ _ => Iff.rfl⟩
  have hXfin : X.Finite := Set.toFinite X
  have hΩfin : Ω.Finite := Set.toFinite Ω
  have hXcard : Nat.card X = 8 := by
    have e : zGroup Ω ≃ X :=
      Equiv.ofBijective (fun e => (⟨q * e.1, (hmemX _).mpr ⟨e.1, e.2, rfl⟩⟩ : X))
        ⟨fun a b hab => Subtype.ext (mul_left_cancel (congrArg Subtype.val hab)),
          fun x => by
            obtain ⟨e, he, hx⟩ := (hmemX x.1).mp x.2
            exact ⟨⟨e, he⟩, Subtype.ext hx.symm⟩⟩
    rw [← Nat.card_congr e, h.card_zGroup]
  set Xs := hXfin.toFinset with hXs_def
  set Os := hΩfin.toFinset with hOs_def
  have hmemXs : ∀ x, x ∈ Xs ↔ x ∈ X := fun x => hXfin.mem_toFinset
  have hmemOs : ∀ L, L ∈ Os ↔ L ∈ Ω := fun L => hΩfin.mem_toFinset
  have hXs8 : Xs.card = 8 := by
    rw [hXs_def, ← Set.ncard_eq_toFinset_card X hXfin, ← Nat.card_coe_set_eq X, hXcard]
  have hOs14 : Os.card = 14 := by
    rw [hOs_def, ← Set.ncard_eq_toFinset_card Ω hΩfin, h.ncard_eq_fourteen]
  have hA : ∀ L ∈ Ω, (Xs.filter (fun x => r x L)).card = 2 := by
    intro L hL
    have hDfin : {d : G | d ∈ zGroup Ω ∧ ∀ y ∈ L, (q * d) * y = y * (q * d)}.Finite :=
      Set.toFinite _
    have hDcard := h.ncard_centralized_coset hq hq0 hL
    rw [Set.ncard_eq_toFinset_card _ hDfin] at hDcard
    rw [← hDcard]
    apply Finset.card_nbij' (fun x => q⁻¹ * x) (fun d => q * d)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, hmemXs, hr] at hx
      obtain ⟨e, he, rfl⟩ := (hmemX x).mp hx.1
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq, inv_mul_cancel_left]
      refine ⟨he, ?_⟩
      intro y hy
      exact hx.2 y hy
    · intro d hd
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hd
      simp only [Finset.mem_coe, Finset.mem_filter, hmemXs, hr]
      exact ⟨(hmemX _).mpr ⟨d, hd.1, rfl⟩, hd.2⟩
    · intro x _
      exact mul_inv_cancel_left q x
    · intro d _
      exact inv_mul_cancel_left q d
  have hconj : ∀ (k a b : G) (L : Subgroup G), k * a * k⁻¹ = b → (∀ y ∈ L, a * y = y * a) →
      ∀ y ∈ conjSub k L, b * y = y * b := by
    intro k a b L hkab hL y hy
    have hz : k⁻¹ * y * k ∈ L := mem_conjSub_iff.mp hy
    have hcomm := hL _ hz
    rw [← hkab]
    calc k * a * k⁻¹ * y = k * (a * (k⁻¹ * y * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * y * k) * a) * k⁻¹ := by rw [hcomm]
      _ = y * (k * a * k⁻¹) := by group
  have hB : ∀ x ∈ X, ∀ x' ∈ X,
      (Os.filter (fun L => r x L)).card = (Os.filter (fun L => r x' L)).card := by
    intro x hx x' hx'
    obtain ⟨e, he, rfl⟩ := (hmemX x).mp hx
    obtain ⟨e', he', rfl⟩ := (hmemX x').mp hx'
    obtain ⟨g, hg⟩ := h.exists_conj_coset_eq hq hq0 hqD he he'
    apply Finset.card_nbij' (conjSub g) (conjSub g⁻¹)
    · intro L hL
      simp only [Finset.mem_coe, Finset.mem_filter, hmemOs, hr] at hL ⊢
      exact ⟨h.hyp.conjInvariant g L hL.1,
        hconj g (q * e) (q * e') L hg hL.2⟩
    · intro L hL
      simp only [Finset.mem_coe, Finset.mem_filter, hmemOs, hr] at hL ⊢
      have hg' : g⁻¹ * (q * e') * g⁻¹⁻¹ = q * e := by
        rw [inv_inv, ← hg]
        group
      exact ⟨h.hyp.conjInvariant g⁻¹ L hL.1,
        hconj g⁻¹ (q * e') (q * e) L hg' hL.2⟩
    · intro L _
      exact conjSub_inv_conjSub g L
    · intro L _
      exact conjSub_conjSub_inv g L
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ X := ⟨q, (hmemX q).mpr ⟨1, (zGroup Ω).one_mem, by group⟩⟩
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Xs) (t := Os)
    (r := r)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  have hLsum : ∑ x ∈ Xs, (Os.filter (fun L => r x L)).card =
      Xs.card * (Os.filter (fun L => r x₀ L)).card := by
    rw [Finset.sum_congr rfl (fun x hx => hB x ((hmemXs x).mp hx) x₀ hx₀), Finset.sum_const,
      smul_eq_mul]
  have hRsum : ∑ L ∈ Os, (Xs.filter (fun x => r x L)).card = Os.card * 2 := by
    rw [Finset.sum_congr rfl (fun L hL => hA L ((hmemOs L).mp hL)), Finset.sum_const, smul_eq_mul]
  rw [hLsum, hRsum, hXs8, hOs14] at hdc
  omega

theorem exists_star {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {u v : G}
    (hu : IsUniqueInvolution K u) (hv : IsUniqueInvolution J v) (huv : u ≠ v) :
    ∃ k ∈ K, ∃ M ∈ Ω, M = conjSub k J ∧ IsUniqueInvolution M (u * v) := by
  have huD : u ∈ zGroup Ω := deq2_involution_mem h hK hu
  have hvD : v ∈ zGroup Ω := deq2_involution_mem h hJ hv
  have hvv : v * v = 1 := h.zGroup_mul_self v hvD
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := h.dNorm K hK hvD
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hu (h.isQuatSub_of_mem hK) (h.card K hK)
  have htK : ∀ x ∈ K, v * x * v⁻¹ ∈ K := fun x hx => (Subgroup.mem_normalizer_iff.mp hvN x).mp hx
  obtain ⟨x₀, hx₀K, hx₀⟩ := h.exists_not_commute_of_ne hK hJ hu hv huv
  obtain ⟨k, hk, hkv⟩ :=
    exists_conj_eq_mul_of_not_comm hu hi hj hii hjj hji hNF hvv htK ⟨x₀, hx₀K, hx₀⟩
  rw [inv_eq_of_mul_eq_one_right hvv] at hkv
  have h1 : v * k * v = u * k := hkv
  have hcomm : v * u = u * v := h.zGroup_comm v hvD u huD
  have e : k * v = u * v * k := by
    calc k * v = (v * v) * k * v := by rw [hvv, one_mul]
      _ = v * (v * k * v) := by group
      _ = v * (u * k) := by rw [h1]
      _ = (v * u) * k := by group
      _ = (u * v) * k := by rw [hcomm]
  have hkconj : k * v * k⁻¹ = u * v := by
    calc k * v * k⁻¹ = (u * v * k) * k⁻¹ := by rw [e]
      _ = u * v := by group
  refine ⟨k, hk, conjSub k J, h.hyp.conjInvariant k J hJ, rfl, ?_⟩
  have hc := hv.conj k
  rw [hkconj] at hc
  exact hc

theorem flipVal_eq_zero_of_mul {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω) (h₃ : K₃ ∈ Ω)
    {u v w : G} (hu : IsUniqueInvolution K₁ u) (hv : IsUniqueInvolution K₂ v)
    (hw : IsUniqueInvolution K₃ w) (huv : u ≠ v) (hw' : w = u * v) {q : G}
    (hq : q ∈ pCore 2 G) (hq₁ : flipVal K₁ q = 0) (hq₂ : flipVal K₂ q = 0) :
    flipVal K₃ q = 0 := by
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  obtain ⟨k, hk, M, hM, hMk, hMuv⟩ := h.exists_star h₁ h₂ hu hv huv
  have hMw : IsUniqueInvolution M w := hw' ▸ hMuv
  have hMtw : M ∈ twinSet Ω K₃ := ⟨hM, w, hw, hMw⟩
  have huD : u ∈ zGroup Ω := deq2_involution_mem h h₁ hu
  have hq₁' : conjSub q K₁ = K₁ := deq2_flipVal_eq_zero_iff.mp hq₁
  have hq₂' : conjSub q K₂ = K₂ := deq2_flipVal_eq_zero_iff.mp hq₂
  have hqk : q * k * q⁻¹ ∈ K₁ := by
    have := conj_mem_conjSub (n := q) hk
    rwa [hq₁'] at this
  have hc : (q * k * q⁻¹) * k⁻¹ ∈ K₁ ⊓ pCore 2 G := by
    refine ⟨K₁.mul_mem hqk (K₁.inv_mem hk), ?_⟩
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCore 2 G).mul_mem hq (hQn.conj_mem q⁻¹ ((pCore 2 G).inv_mem hq) k)
  rw [h.inf_pCore h₁ hu] at hc
  obtain ⟨c, hcdef⟩ : ∃ c, c = (q * k * q⁻¹) * k⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hc1 := deq2_eq_one_or_eq_of_mem_zpowers hu.sq hu.ne_one hc
  have hqkc : q * k * q⁻¹ = c * k := by rw [hcdef]; group
  have hcM : conjSub c M = M := by
    rcases hc1 with h1 | h1
    · rw [h1, conjSub_one]
    · rw [h1]
      exact mem_normalizer_iff_conjSub_eq.mp (h.dNorm M hM huD)
  have hconjM : conjSub q M = M := by
    calc conjSub q M = conjSub (q * k) K₂ := by rw [hMk, ← conjSub_mul]
      _ = conjSub (q * k * q⁻¹ * q) K₂ := by group
      _ = conjSub (q * k * q⁻¹) (conjSub q K₂) := by rw [← conjSub_mul]
      _ = conjSub (q * k * q⁻¹) K₂ := by rw [hq₂']
      _ = conjSub (c * k) K₂ := by rw [hqkc]
      _ = conjSub c (conjSub k K₂) := by rw [conjSub_mul]
      _ = M := by rw [← hMk, hcM]
  have hflip := h.flipVal_eq_of_mem_twinSet h₃ hMtw hq
  rw [← hflip]
  exact deq2_flipVal_eq_zero_iff.mpr hconjM

private theorem deq2_index_normalizer {L : Subgroup G} (hL : L ∈ Ω) :
    (Subgroup.normalizer (L : Set G)).index = 14 := by
  letI act : MulAction G Ω :=
    { smul := fun g M => ⟨conjSub g M.1, h.hyp.conjInvariant g M.1 M.2⟩
      one_smul := fun M => Subtype.ext (conjSub_one M.1)
      mul_smul := fun a b M => Subtype.ext (conjSub_mul a b M.1) }
  haveI : MulAction.IsPretransitive G Ω := ⟨fun M M' => by
    obtain ⟨g, hg⟩ := h.trans M.1 M.2 M'.1 M'.2
    exact ⟨g, Subtype.ext hg⟩⟩
  have hstab : MulAction.stabilizer G (⟨L, hL⟩ : Ω) = Subgroup.normalizer (L : Set G) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_normalizer_iff_conjSub_eq]
    constructor
    · intro hg
      exact congrArg Subtype.val hg
    · intro hg
      exact Subtype.ext hg
  rw [← hstab, MulAction.index_stabilizer_of_transitive G, Nat.card_coe_set_eq,
    h.ncard_eq_fourteen]

theorem card_pCore_ne_sixteen : Nat.card (pCore 2 G) ≠ 16 := by
  intro h16
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  haveI : (zGroup Ω).Normal := h.zGroup_normal
  haveI : (pCore 2 G).Normal := hQn
  have hcardQ : (pCore 2 G).index = 168 := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.index_centralizer_zGroup
  have hG : Nat.card G = 2688 := by
    have := Subgroup.card_mul_index (pCore 2 G)
    rw [h16, hcardQ] at this
    omega
  obtain ⟨L, hL, -⟩ := h.exists_ne
  have hN : Nat.card (Subgroup.normalizer (L : Set G)) = 192 := by
    have := Subgroup.card_mul_index (Subgroup.normalizer (L : Set G))
    rw [h.deq2_index_normalizer hL, hG] at this
    omega
  have hNQ : Subgroup.normalizer (L : Set G) ⊓ pCore 2 G = zGroup Ω := by
    have hDle : zGroup Ω ≤ Subgroup.normalizer (L : Set G) ⊓ pCore 2 G :=
      le_inf (h.dNorm L hL) h.zGroup_le_pCore
    obtain ⟨q, hqQ, hq1⟩ := h.exists_flip hL
    have hqN : q ∉ Subgroup.normalizer (L : Set G) := by
      intro hqN
      have h0 := deq2_flipVal_eq_zero_iff.mpr (mem_normalizer_iff_conjSub_eq.mp hqN)
      rw [hq1] at h0
      exact one_ne_zero h0
    have hQsub : Subgroup.normalizer (L : Set G) ⊓ pCore 2 G ≤ pCore 2 G := inf_le_right
    have hne : Subgroup.normalizer (L : Set G) ⊓ pCore 2 G ≠ pCore 2 G := by
      intro heq
      apply hqN
      have hq' : q ∈ Subgroup.normalizer (L : Set G) ⊓ pCore 2 G := by
        rw [heq]
        exact hqQ
      exact hq'.1
    obtain ⟨c, hc⟩ : ∃ c, c = Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓ pCore 2 G :
        Subgroup G) := ⟨_, rfl⟩
    have hdvd : c ∣ 16 := by
      rw [hc, ← h16]
      exact Subgroup.card_dvd_of_le hQsub
    have hge : 8 ≤ c := by
      rw [hc, ← h.card_zGroup]
      exact Subgroup.card_le_of_le hDle
    have hlt : c ≠ 16 := by
      rw [hc]
      intro h16'
      apply hne
      apply Subgroup.eq_of_le_of_card_ge hQsub
      rw [h16', h16]
    have hc8 : c ≤ 8 := by
      have hle16 : c ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases c <;> first | omega | (norm_num at hdvd) | exact absurd rfl hlt
    exact (Subgroup.eq_of_le_of_card_ge hDle (by rw [h.card_zGroup, ← hc]; exact hc8)).symm
  exact deq2_no_quotient_split (zGroup Ω) (pCore 2 G) (Subgroup.normalizer (L : Set G))
    h.zGroup_le_pCore h.card_zGroup h16 hG (h.dNorm L hL) hNQ hN h.commutator_eq_top

private theorem deq2_hyp_pair {x y : G} (hxD : x ∈ zGroup Ω) (hyD : y ∈ zGroup Ω)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    ∃ H : Subgroup G, IsHyp Ω H ∧ ∀ g : G, g ∈ H ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have hxx : x * x = 1 := h.zGroup_mul_self x hxD
  have hyy : y * y = 1 := h.zGroup_mul_self y hyD
  have hyx : y * x = x * y := (h.zGroup_comm x hxD y hyD).symm
  have hxyD : x * y ∈ zGroup Ω := (zGroup Ω).mul_mem hxD hyD
  have hxy2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hyx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  have hyxy : y * (x * y) = x := by
    calc y * (x * y) = (y * x) * y := by group
      _ = (x * y) * y := by rw [hyx]
      _ = x * (y * y) := by group
      _ = x := by rw [hyy, mul_one]
  have hxy1 : x * y * x = y := by
    calc x * y * x = x * (y * x) := by group
      _ = x * (x * y) := by rw [hyx]
      _ = (x * x) * y := by group
      _ = y := by rw [hxx, one_mul]
  have hxy' : x * y * y = x := by
    calc x * y * y = x * (y * y) := by group
      _ = x := by rw [hyy, mul_one]
  have hxxy : x * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
  have hxy_ne1 : x * y ≠ 1 := by
    intro e
    apply hxy
    calc x = x * 1 := (mul_one x).symm
      _ = x * (x * y) := by rw [e]
      _ = y := hxxy
  have hx_ne_xy : x ≠ x * y := by
    intro e
    apply hy1
    calc y = x * (x * y) := hxxy.symm
      _ = x * x := by rw [← e]
      _ = 1 := hxx
  have hy_ne_xy : y ≠ x * y := by
    intro e
    apply hx1
    calc x = y * (x * y) := hyxy.symm
      _ = y * y := by rw [← e]
      _ = 1 := hyy
  let H : Subgroup G :=
    { carrier := {1, x, y, x * y}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hxx, hyy, hyx, hxy2, hxxy, hyxy, hxy1, hxy']
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · simp [inv_eq_of_mul_eq_one_right hxx]
        · simp [inv_eq_of_mul_eq_one_right hyy]
        · simp [inv_eq_of_mul_eq_one_right hxy2] }
  have hH : (H : Set G) = {1, x, y, x * y} := rfl
  have hxnotin : x ∉ ({y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy, hx_ne_xy⟩
  have h1notin : (1 : G) ∉ ({x, y, x * y} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hx1.symm, hy1.symm, hxy_ne1.symm⟩
  have hcard : Nat.card H = 4 := by
    show Nat.card (H : Set G) = 4
    rw [Nat.card_coe_set_eq, hH, Set.ncard_insert_of_notMem h1notin,
      Set.ncard_insert_of_notMem hxnotin, Set.ncard_pair hy_ne_xy]
  refine ⟨H, ?_, fun g => Iff.rfl⟩
  unfold IsHyp
  refine ⟨?_, hcard⟩
  intro g hg
  have hg' : g = 1 ∨ g = x ∨ g = y ∨ g = x * y := hg
  rcases hg' with rfl | rfl | rfl | rfl
  · exact (zGroup Ω).one_mem
  · exact hxD
  · exact hyD
  · exact hxyD

private theorem deq2_closure3 {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (h₃ : K₃ ∈ Ω) {u v w : G} (hu : IsUniqueInvolution K₁ u) (hv : IsUniqueInvolution K₂ v)
    (hw : IsUniqueInvolution K₃ w) (huv : u ≠ v) (hw' : w = u * v) {q : G}
    (hq : q ∈ pCore 2 G) :
    (flipVal K₁ q = 0 → flipVal K₂ q = 0 → flipVal K₃ q = 0) ∧
      (flipVal K₂ q = 0 → flipVal K₃ q = 0 → flipVal K₁ q = 0) ∧
      (flipVal K₁ q = 0 → flipVal K₃ q = 0 → flipVal K₂ q = 0) := by
  have huD := deq2_involution_mem h h₁ hu
  have hvD := deq2_involution_mem h h₂ hv
  have hcomm : u * v = v * u := h.zGroup_comm u huD v hvD
  have hvv : v * v = 1 := h.zGroup_mul_self v hvD
  have huu : u * u = 1 := h.zGroup_mul_self u huD
  have hu' : u = v * w := by
    rw [hw']
    calc u = u * (v * v) := by rw [hvv, mul_one]
      _ = (u * v) * v := by group
      _ = (v * u) * v := by rw [hcomm]
      _ = v * (u * v) := by group
  have hv' : v = u * w := by
    rw [hw']
    calc v = (u * u) * v := by rw [huu, one_mul]
      _ = u * (u * v) := by group
  have hvw : v ≠ w := by
    intro e
    apply hu.ne_one
    calc u = u * (v * v) := by rw [hvv, mul_one]
      _ = (u * v) * v := by group
      _ = v * v := by rw [← hw', ← e]
      _ = 1 := hvv
  have huw : u ≠ w := by
    intro e
    apply hv.ne_one
    calc v = (u * u) * v := by rw [huu, one_mul]
      _ = u * (u * v) := by group
      _ = u * w := by rw [← hw']
      _ = u * u := by rw [← e]
      _ = 1 := huu
  exact ⟨fun a b => h.flipVal_eq_zero_of_mul h₁ h₂ h₃ hu hv hw huv hw' hq a b,
    fun a b => h.flipVal_eq_zero_of_mul h₂ h₃ h₁ hv hw hu hvw hu' hq a b,
    fun a b => h.flipVal_eq_zero_of_mul h₁ h₃ h₂ hu hw hv huw hv' hq a b⟩

private theorem deq2_pattern_const {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (h₃ : K₃ ∈ Ω) {u v w : G} (hu : IsUniqueInvolution K₁ u) (hv : IsUniqueInvolution K₂ v)
    (hw : IsUniqueInvolution K₃ w) (huv : u ≠ v) (hw' : w = u * v) {q₀ : G}
    (hq₀ : q₀ ∈ pCore 2 G) (h10 : flipVal K₁ q₀ = 1) (h20 : flipVal K₂ q₀ = 1)
    (h30 : flipVal K₃ q₀ = 1) :
    ∀ q ∈ pCore 2 G, flipVal K₁ q = flipVal K₂ q ∧ flipVal K₂ q = flipVal K₃ q := by
  intro q hq
  obtain ⟨c1, c2, c3⟩ := h.deq2_closure3 h₁ h₂ h₃ hu hv hw huv hw' hq
  have hqq : q * q₀ ∈ pCore 2 G := (pCore 2 G).mul_mem hq hq₀
  obtain ⟨d1, d2, d3⟩ := h.deq2_closure3 h₁ h₂ h₃ hu hv hw huv hw' hqq
  have e1 : flipVal K₁ (q * q₀) = flipVal K₁ q + 1 := by
    rw [h.flipVal_mul h₁ hq hq₀, h10]
  have e2 : flipVal K₂ (q * q₀) = flipVal K₂ q + 1 := by
    rw [h.flipVal_mul h₂ hq hq₀, h20]
  have e3 : flipVal K₃ (q * q₀) = flipVal K₃ q + 1 := by
    rw [h.flipVal_mul h₃ hq hq₀, h30]
  rw [e1, e2, e3] at d1 d2 d3
  exact deq2_zmod_const _ _ _ c1 c2 c3 d1 d2 d3

private theorem deq2_bad_global {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω)
    (h₃ : K₃ ∈ Ω) {u v w : G} (hu : IsUniqueInvolution K₁ u) (hv : IsUniqueInvolution K₂ v)
    (hw : IsUniqueInvolution K₃ w) (huv : u ≠ v) (hw' : w = u * v) {q₀ : G}
    (hq₀ : q₀ ∈ pCore 2 G) (h10 : flipVal K₁ q₀ = 1) (h20 : flipVal K₂ q₀ = 1)
    (h30 : flipVal K₃ q₀ = 1) : False := by
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  have huD := deq2_involution_mem h h₁ hu
  have hvD := deq2_involution_mem h h₂ hv
  obtain ⟨H₀, hH₀, hH₀mem⟩ := h.deq2_hyp_pair huD hvD hu.ne_one hv.ne_one huv
  have hconst : ∀ L ∈ Ω, ∀ q ∈ pCore 2 G, flipVal L q = flipVal K₁ q := by
    intro L hL q hq
    obtain ⟨x, hx⟩ := h.exists_isUniqueInvolution hL
    have hxD := deq2_involution_mem h hL hx
    have hx1 := hx.ne_one
    by_cases hxu : x = u
    · rw [hxu] at hx
      exact h.flipVal_eq_of_mem_twinSet h₁ ⟨hL, u, hu, hx⟩ hq
    · obtain ⟨H, hH, hHmem⟩ := h.deq2_hyp_pair huD hxD hu.ne_one hx1 (Ne.symm hxu)
      obtain ⟨g, hg⟩ := h.exists_conj_hyp hH₀ hH
      have huv' : g * u * g⁻¹ ≠ g * v * g⁻¹ := by
        intro e
        apply huv
        calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
          _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [e]
          _ = v := by group
      have hw'' : g * w * g⁻¹ = g * u * g⁻¹ * (g * v * g⁻¹) := by
        rw [hw']
        group
      have hq₀' : g * q₀ * g⁻¹ ∈ pCore 2 G := hQn.conj_mem q₀ hq₀ g
      have h10' : flipVal (conjSub g K₁) (g * q₀ * g⁻¹) = 1 := by
        rw [h.flipVal_conj h₁ g hq₀, h10]
      have h20' : flipVal (conjSub g K₂) (g * q₀ * g⁻¹) = 1 := by
        rw [h.flipVal_conj h₂ g hq₀, h20]
      have h30' : flipVal (conjSub g K₃) (g * q₀ * g⁻¹) = 1 := by
        rw [h.flipVal_conj h₃ g hq₀, h30]
      have hT := h.deq2_pattern_const (h.hyp.conjInvariant g K₁ h₁)
        (h.hyp.conjInvariant g K₂ h₂) (h.hyp.conjInvariant g K₃ h₃)
        (hu.conj g) (hv.conj g) (hw.conj g) huv' hw'' hq₀' h10' h20' h30'
      have hmemH : ∀ y ∈ H, y ≠ 1 → ∀ M ∈ Ω, IsUniqueInvolution M y →
          ∀ q' ∈ pCore 2 G, flipVal M q' = flipVal (conjSub g K₁) q' := by
        intro y hyH hy1 M hM hMy q' hq'
        have hy0 : g⁻¹ * y * g ∈ H₀ := by
          rw [← hg] at hyH
          exact mem_conjSub_iff.mp hyH
        rcases (hH₀mem (g⁻¹ * y * g)).mp hy0 with h1 | h1 | h1 | h1
        · exfalso
          apply hy1
          calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
            _ = g * 1 * g⁻¹ := by rw [h1]
            _ = 1 := by group
        · have hy : IsUniqueInvolution (conjSub g K₁) y := by
            have e : g * u * g⁻¹ = y := by
              rw [← h1]
              group
            rw [← e]
            exact hu.conj g
          exact h.flipVal_eq_of_mem_twinSet (h.hyp.conjInvariant g K₁ h₁) ⟨hM, y, hy, hMy⟩ hq'
        · have hy : IsUniqueInvolution (conjSub g K₂) y := by
            have e : g * v * g⁻¹ = y := by
              rw [← h1]
              group
            rw [← e]
            exact hv.conj g
          exact (h.flipVal_eq_of_mem_twinSet (h.hyp.conjInvariant g K₂ h₂) ⟨hM, y, hy, hMy⟩
            hq').trans (hT q' hq').1.symm
        · have hy : IsUniqueInvolution (conjSub g K₃) y := by
            have e : g * w * g⁻¹ = y := by
              rw [hw', ← h1]
              group
            rw [← e]
            exact hw.conj g
          exact (h.flipVal_eq_of_mem_twinSet (h.hyp.conjInvariant g K₃ h₃) ⟨hM, y, hy, hMy⟩
            hq').trans ((hT q' hq').2.symm.trans (hT q' hq').1.symm)
      have hxH : x ∈ H := (hHmem x).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have huH : u ∈ H := (hHmem u).mpr (Or.inr (Or.inl rfl))
      have hx' := hmemH x hxH hx1 L hL hx q hq
      have hu' := hmemH u huH hu.ne_one K₁ h₁ hu q hq
      exact hx'.trans hu'.symm
  have hker : ∀ q ∈ pCore 2 G, flipVal K₁ q = 0 → q ∈ zGroup Ω := by
    intro q hq hq0
    refine h.mem_zGroup_of_flipVal_eq_zero hq ?_
    intro L hL
    rw [hconst L hL q hq, hq0]
  have hD0 : ∀ d ∈ zGroup Ω, flipVal K₁ d = 0 := fun d hd =>
    deq2_flipVal_eq_zero_iff.mpr (mem_normalizer_iff_conjSub_eq.mp (h.dNorm K₁ h₁ hd))
  obtain ⟨q₁, hq₁Q, hq₁⟩ := h.exists_flip h₁
  have hq1D : q₁ ∉ zGroup Ω := fun hD => by
    have h0 := hD0 q₁ hD
    rw [hq₁] at h0
    exact one_ne_zero h0
  have hrel : (zGroup Ω).relIndex (pCore 2 G) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨q₁, hq₁Q⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ zGroup Ω
    · right
      refine ⟨hb, fun h1 => hq1D ?_⟩
      exact ((zGroup Ω).mul_mem_cancel_left hb).mp h1
    · left
      have hbq : flipVal K₁ (b : G) ≠ 0 := fun h0 => hb (hker b b.2 h0)
      have hbq1 : flipVal K₁ (b : G) = 1 := (deq2_flipVal_cases K₁ b).resolve_left hbq
      have hbq' : flipVal K₁ ((b : G) * q₁) = 0 := by
        rw [h.flipVal_mul h₁ b.2 hq₁Q, hbq1, hq₁]
        decide
      exact ⟨hker _ ((pCore 2 G).mul_mem b.2 hq₁Q) hbq', hb⟩
  have hcard : Nat.card (pCore 2 G) = 16 := by
    have h2 := Subgroup.relIndex_mul_card (H := zGroup Ω) (K := pCore 2 G)
    rw [inf_eq_left.mpr h.zGroup_le_pCore, hrel, h.card_zGroup] at h2
    omega
  exact h.card_pCore_ne_sixteen hcard

theorem flipVal_add_of_mul {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ Ω) (h₂ : K₂ ∈ Ω) (h₃ : K₃ ∈ Ω)
    {u v w : G} (hu : IsUniqueInvolution K₁ u) (hv : IsUniqueInvolution K₂ v)
    (hw : IsUniqueInvolution K₃ w) (huv : u ≠ v) (hw' : w = u * v) {q : G}
    (hq : q ∈ pCore 2 G) : flipVal K₃ q = flipVal K₁ q + flipVal K₂ q := by
  obtain ⟨c1, c2, c3⟩ := h.deq2_closure3 h₁ h₂ h₃ hu hv hw huv hw' hq
  by_contra hne
  obtain ⟨ha, hb, hc⟩ := deq2_zmod_three _ _ _ c1 c2 c3 hne
  exact h.deq2_bad_global h₁ h₂ h₃ hu hv hw huv hw' hq ha hb hc

open Classical in
@[expose] noncomputable def deq2Lam (Ω : Set (Subgroup G)) (Lf : G → Subgroup G) (q x : G) :
    ZMod 2 :=
  if x ∈ zGroup Ω ∧ x ≠ 1 then flipVal (Lf x) q else 0

@[expose] def deq2Dual (Ω : Set (Subgroup G)) : Set (G → ZMod 2) :=
  {F | F 1 = 0 ∧ (∀ x, x ∉ zGroup Ω → F x = 0) ∧
    ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, F (x * y) = F x + F y}

open Classical in
@[expose] noncomputable def deq2Fh (Ω : Set (Subgroup G)) (H : Subgroup G) : G → ZMod 2 :=
  fun x => if x ∈ zGroup Ω ∧ x ∉ H then 1 else 0

private theorem deq2_hyp_relIndex {H : Subgroup G} (hH : IsHyp Ω H) :
    H.relIndex (zGroup Ω) = 2 := by
  unfold IsHyp at hH
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := zGroup Ω)
  rw [inf_eq_left.mpr hH.1, hH.2, h.card_zGroup] at h1
  omega

private theorem deq2_hyp_mul_mem {H : Subgroup G} (hH : IsHyp Ω H) {x y : G}
    (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω) (hxH : x ∉ H) (hyH : y ∉ H) : x * y ∈ H := by
  have hi := h.deq2_hyp_relIndex hH
  unfold Subgroup.relIndex at hi
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hi
  have haD : (a : G) ∈ zGroup Ω := a.2
  have hxa : x * (a : G) ∈ H := by
    rcases ha ⟨x, hx⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hxH
  have hya : y * (a : G) ∈ H := by
    rcases ha ⟨y, hy⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hyH
  have haa : (a : G) * a = 1 := h.zGroup_mul_self a haD
  have e : (x * (a : G)) * (y * (a : G)) = x * y := by
    calc (x * (a : G)) * (y * (a : G)) = x * ((a : G) * y) * (a : G) := by group
      _ = x * (y * (a : G)) * (a : G) := by rw [h.zGroup_comm a haD y hy]
      _ = x * y * ((a : G) * a) := by group
      _ = x * y := by rw [haa, mul_one]
  rw [← e]
  exact H.mul_mem hxa hya

private theorem deq2_fh_mem_dual {H : Subgroup G} (hH : IsHyp Ω H) :
    deq2Fh Ω H ∈ deq2Dual Ω := by
  have hHD : H ≤ zGroup Ω := hH.1
  refine ⟨?_, ?_, ?_⟩
  · simp [deq2Fh, H.one_mem]
  · intro x hx
    simp [deq2Fh, hx]
  · intro x hx y hy
    have hxyD : x * y ∈ zGroup Ω := (zGroup Ω).mul_mem hx hy
    by_cases hxH : x ∈ H <;> by_cases hyH : y ∈ H
    · have hxyH : x * y ∈ H := H.mul_mem hxH hyH
      simp [deq2Fh, hxH, hyH, hxyH]
    · have hxyH : x * y ∉ H := fun hm => hyH (by
        have := H.mul_mem (H.inv_mem hxH) hm
        simpa using this)
      simp [deq2Fh, hxyD, hx, hy, hxH, hyH, hxyH]
    · have hxyH : x * y ∉ H := fun hm => hxH (by
        have := H.mul_mem hm (H.inv_mem hyH)
        simpa using this)
      simp [deq2Fh, hxyD, hx, hy, hxH, hyH, hxyH]
    · have hxyH : x * y ∈ H := h.deq2_hyp_mul_mem hH hx hy hxH hyH
      simp [deq2Fh, hxyD, hx, hy, hxH, hyH, hxyH] <;> decide

private theorem deq2_dual_eq_fh {F : G → ZMod 2} (hF : F ∈ deq2Dual Ω) (hF0 : F ≠ 0) :
    ∃ H : Subgroup G, IsHyp Ω H ∧ F = deq2Fh Ω H := by
  obtain ⟨h1, h2, h3⟩ := hF
  have hc1 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, F x₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext fun x => hcon x)
  have hx₀D : x₀ ∈ zGroup Ω := by
    by_contra hn
    exact hx₀ (h2 x₀ hn)
  have hx₀one : F x₀ = 1 := hc1 _ hx₀
  let H : Subgroup G :=
    { carrier := {x | x ∈ zGroup Ω ∧ F x = 0}
      mul_mem' := by
        rintro a b ⟨ha, ha0⟩ ⟨hb, hb0⟩
        exact ⟨(zGroup Ω).mul_mem ha hb, by rw [h3 a ha b hb, ha0, hb0, add_zero]⟩
      one_mem' := ⟨(zGroup Ω).one_mem, h1⟩
      inv_mem' := by
        rintro a ⟨ha, ha0⟩
        refine ⟨(zGroup Ω).inv_mem ha, ?_⟩
        have := h3 a ha a⁻¹ ((zGroup Ω).inv_mem ha)
        rw [mul_inv_cancel, h1, ha0, zero_add] at this
        exact this.symm }
  have hHD : H ≤ zGroup Ω := fun x hx => hx.1
  have hmemH : ∀ x, x ∈ H ↔ x ∈ zGroup Ω ∧ F x = 0 := fun x => Iff.rfl
  have hrel : H.relIndex (zGroup Ω) = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨x₀, hx₀D⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb0 : F (b : G) = 0
    · right
      refine ⟨(hmemH _).mpr ⟨b.2, hb0⟩, fun hm => ?_⟩
      have hm' := (hmemH _).mp hm
      rw [h3 _ b.2 _ hx₀D, hb0, hx₀one] at hm'
      exact absurd hm'.2 (by decide)
    · left
      have hb1 : F (b : G) = 1 := hc1 _ hb0
      refine ⟨(hmemH _).mpr ⟨(zGroup Ω).mul_mem b.2 hx₀D, ?_⟩, fun hm => hb0 (hm.2)⟩
      rw [h3 _ b.2 _ hx₀D, hb1, hx₀one]
      decide
  have hHcard : Nat.card H = 4 := by
    have h1' := Subgroup.relIndex_mul_card (H := H) (K := zGroup Ω)
    rw [inf_eq_left.mpr hHD, hrel, h.card_zGroup] at h1'
    omega
  refine ⟨H, ⟨hHD, hHcard⟩, funext fun x => ?_⟩
  unfold deq2Fh
  by_cases hxD : x ∈ zGroup Ω
  · by_cases hFx : F x = 0
    · have hxH : x ∈ H := (hmemH x).mpr ⟨hxD, hFx⟩
      simp [hxH, hFx]
    · have hxH : x ∉ H := fun hm => hFx ((hmemH x).mp hm).2
      simp [hxD, hxH, hc1 _ hFx]
  · simp [hxD, h2 x hxD]

private theorem deq2_dual_ncard : (deq2Dual Ω).ncard = 8 := by
  have hfh0 : ∀ H : Subgroup G, IsHyp Ω H → deq2Fh Ω H ≠ 0 := by
    intro H hH hfh
    obtain ⟨x, hxD, hxH⟩ : ∃ x, x ∈ zGroup Ω ∧ x ∉ H := by
      by_contra hcon
      push_neg at hcon
      have hHtop : zGroup Ω ≤ H := fun x hx => hcon x hx
      have := Subgroup.card_le_of_le hHtop
      unfold IsHyp at hH
      rw [h.card_zGroup, hH.2] at this
      omega
    have := congrFun hfh x
    simp [deq2Fh, hxD, hxH] at this
  have hinj : Set.InjOn (deq2Fh Ω) {H : Subgroup G | IsHyp Ω H} := by
    intro H hH H' hH' hHH'
    have hzero : ∀ (K : Subgroup G), IsHyp Ω K → ∀ x, x ∈ K → deq2Fh Ω K x = 0 := by
      intro K hK x hx
      have hxD : x ∈ zGroup Ω := (show K ≤ zGroup Ω from hK.1) hx
      simp [deq2Fh, hx]
    ext x
    constructor
    · intro hx
      have hx0 := hzero H hH x hx
      rw [hHH'] at hx0
      have hxD : x ∈ zGroup Ω := (show H ≤ zGroup Ω from hH.1) hx
      by_contra hn
      simp [deq2Fh, hxD, hn] at hx0
    · intro hx
      have hx0 := hzero H' hH' x hx
      rw [← hHH'] at hx0
      have hxD : x ∈ zGroup Ω := (show H' ≤ zGroup Ω from hH'.1) hx
      by_contra hn
      simp [deq2Fh, hxD, hn] at hx0
  have hset : deq2Dual Ω = insert 0 (deq2Fh Ω '' {H : Subgroup G | IsHyp Ω H}) := by
    ext F
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hF
      by_cases hF0 : F = 0
      · exact Or.inl hF0
      · obtain ⟨H, hH, hFH⟩ := h.deq2_dual_eq_fh hF hF0
        exact Or.inr ⟨H, hH, hFH.symm⟩
    · rintro (rfl | ⟨H, hH, rfl⟩)
      · refine ⟨rfl, fun _ _ => rfl, fun x _ y _ => by simp⟩
      · exact h.deq2_fh_mem_dual hH
  have hnot : (0 : G → ZMod 2) ∉ deq2Fh Ω '' {H : Subgroup G | IsHyp Ω H} := by
    rintro ⟨H, hH, hfh⟩
    exact hfh0 H hH hfh
  rw [hset, Set.ncard_insert_of_notMem hnot, hinj.ncard_image]
  have := h.card_isHyp
  omega

private theorem deq2_lam_mem_dual {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {q : G} (hq : q ∈ pCore 2 G) : deq2Lam Ω Lf q ∈ deq2Dual Ω := by
  have hlam : ∀ x, x ∈ zGroup Ω → x ≠ 1 → deq2Lam Ω Lf q x = flipVal (Lf x) q := by
    intro x hx hx1
    unfold deq2Lam
    rw [if_pos ⟨hx, hx1⟩]
  have h0 : deq2Lam Ω Lf q 1 = 0 := by
    unfold deq2Lam
    simp
  refine ⟨h0, ?_, ?_⟩
  · intro x hx
    unfold deq2Lam
    simp [hx]
  · intro x hx y hy
    by_cases hx1 : x = 1
    · subst hx1
      simp [h0]
    by_cases hy1 : y = 1
    · subst hy1
      simp [h0]
    by_cases hxy : x = y
    · subst hxy
      have hxx1 : x * x = 1 := h.zGroup_mul_self x hx
      rw [hxx1, h0]
      have hc : ∀ c : ZMod 2, 0 = c + c := by decide
      exact hc _
    · have hxyD : x * y ∈ zGroup Ω := (zGroup Ω).mul_mem hx hy
      have hxx1 : x * x = 1 := h.zGroup_mul_self x hx
      have hxy1 : x * y ≠ 1 := by
        intro e
        apply hxy
        calc x = x * 1 := (mul_one x).symm
          _ = x * (x * y) := by rw [e]
          _ = y := by rw [← mul_assoc, hxx1, one_mul]
      rw [hlam x hx hx1, hlam y hy hy1, hlam (x * y) hxyD hxy1]
      obtain ⟨hK1, hu⟩ := hLf x hx hx1
      obtain ⟨hK2, hv⟩ := hLf y hy hy1
      obtain ⟨hK3, hw⟩ := hLf (x * y) hxyD hxy1
      exact h.flipVal_add_of_mul hK1 hK2 hK3 hu hv hw hxy rfl hq

private theorem deq2_lam_mul {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {q q' : G} (hq : q ∈ pCore 2 G) (hq' : q' ∈ pCore 2 G) :
    deq2Lam Ω Lf (q * q') = deq2Lam Ω Lf q + deq2Lam Ω Lf q' := by
  funext x
  rw [Pi.add_apply]
  unfold deq2Lam
  by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
  · simp only [if_pos hx]
    exact h.flipVal_mul (hLf x hx.1 hx.2).1 hq hq'
  · simp only [if_neg hx, add_zero]

private theorem deq2_lam_D {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {d : G} (hd : d ∈ zGroup Ω) : deq2Lam Ω Lf d = 0 := by
  funext x
  rw [Pi.zero_apply]
  unfold deq2Lam
  by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
  · simp only [if_pos hx]
    exact deq2_flipVal_eq_zero_iff.mpr
      (mem_normalizer_iff_conjSub_eq.mp (h.dNorm _ (hLf x hx.1 hx.2).1 hd))
  · simp only [if_neg hx]

private theorem deq2_lam_eq_zero_iff {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {q : G} (hq : q ∈ pCore 2 G) : deq2Lam Ω Lf q = 0 ↔ q ∈ zGroup Ω := by
  constructor
  · intro hq0
    refine h.mem_zGroup_of_flipVal_eq_zero hq ?_
    intro L hL
    obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
    have hzD := deq2_involution_mem h hL hz
    have hz1 := hz.ne_one
    have h0 : flipVal (Lf z) q = 0 := by
      have := congrFun hq0 z
      unfold deq2Lam at this
      rw [if_pos ⟨hzD, hz1⟩] at this
      simpa using this
    obtain ⟨hK, hKz⟩ := hLf z hzD hz1
    rw [h.flipVal_eq_of_mem_twinSet hK ⟨hL, z, hKz, hz⟩ hq, h0]
  · intro hqD
    exact h.deq2_lam_D hLf hqD

private theorem deq2_lam_conj {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {q : G} (hq : q ∈ pCore 2 G) (g x : G) :
    deq2Lam Ω Lf (g * q * g⁻¹) x = deq2Lam Ω Lf q (g⁻¹ * x * g) := by
  unfold deq2Lam
  by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
  · have hxg : g⁻¹ * x * g ∈ zGroup Ω ∧ g⁻¹ * x * g ≠ 1 := by
      refine ⟨?_, ?_⟩
      · have := h.zGroup_normal.conj_mem x hx.1 g⁻¹
        simpa [mul_assoc] using this
      · intro e
        apply hx.2
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = 1 := by rw [e]; group
    rw [if_pos hx, if_pos hxg]
    have hM : conjSub g⁻¹ (Lf x) ∈ Ω := h.hyp.conjInvariant g⁻¹ _ (hLf x hx.1 hx.2).1
    have hMinv : IsUniqueInvolution (conjSub g⁻¹ (Lf x)) (g⁻¹ * x * g) := by
      have := (hLf x hx.1 hx.2).2.conj g⁻¹
      rwa [inv_inv] at this
    have e1 : flipVal (Lf x) (g * q * g⁻¹) = flipVal (conjSub g⁻¹ (Lf x)) q := by
      conv_lhs => rw [← conjSub_conjSub_inv g (Lf x)]
      exact h.flipVal_conj hM g hq
    have e2 : flipVal (Lf (g⁻¹ * x * g)) q = flipVal (conjSub g⁻¹ (Lf x)) q :=
      h.flipVal_eq_of_mem_twinSet hM
        ⟨(hLf _ hxg.1 hxg.2).1, g⁻¹ * x * g, hMinv, (hLf _ hxg.1 hxg.2).2⟩ hq
    rw [e1, e2]
  · have hxg : ¬ (g⁻¹ * x * g ∈ zGroup Ω ∧ g⁻¹ * x * g ≠ 1) := by
      rintro ⟨h1, h2⟩
      apply hx
      refine ⟨?_, ?_⟩
      · have := h.zGroup_normal.conj_mem _ h1 g
        simpa [mul_assoc] using this
      · intro e
        apply h2
        rw [e]
        group
    rw [if_neg hx, if_neg hxg]

private theorem deq2_lam_one {Lf : G → Subgroup G} : deq2Lam Ω Lf 1 = 0 := by
  funext x
  unfold deq2Lam
  split_ifs with hx
  · exact deq2_flipVal_eq_zero_iff.mpr (conjSub_one _)
  · rfl

private theorem deq2_lam_surj {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {F : G → ZMod 2} (hF : F ∈ deq2Dual Ω) : ∃ q ∈ pCore 2 G, deq2Lam Ω Lf q = F := by
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  by_cases hF0 : F = 0
  · refine ⟨1, (pCore 2 G).one_mem, ?_⟩
    rw [hF0]
    exact h.deq2_lam_one
  · obtain ⟨H, hH, hFH⟩ := h.deq2_dual_eq_fh hF hF0
    obtain ⟨K₀, hK₀, -⟩ := h.exists_ne
    obtain ⟨z₀, hz₀⟩ := h.exists_isUniqueInvolution hK₀
    obtain ⟨q₀, hq₀Q, hq₀⟩ := h.exists_flip hK₀
    have hz₀D := deq2_involution_mem h hK₀ hz₀
    have hz₀1 := hz₀.ne_one
    have hG0 : deq2Lam Ω Lf q₀ ≠ 0 := by
      intro h0
      have h1 := congrFun h0 z₀
      unfold deq2Lam at h1
      rw [if_pos ⟨hz₀D, hz₀1⟩] at h1
      obtain ⟨hK, hKz⟩ := hLf z₀ hz₀D hz₀1
      have htw := h.flipVal_eq_of_mem_twinSet hK₀ ⟨hK, z₀, hz₀, hKz⟩ hq₀Q
      rw [htw, hq₀] at h1
      simp at h1
    obtain ⟨H₀, hH₀, hG0eq⟩ := h.deq2_dual_eq_fh (h.deq2_lam_mem_dual hLf hq₀Q) hG0
    obtain ⟨g, hg⟩ := h.exists_conj_hyp hH₀ hH
    refine ⟨g * q₀ * g⁻¹, hQn.conj_mem q₀ hq₀Q g, ?_⟩
    funext x
    rw [h.deq2_lam_conj hLf hq₀Q g x, hG0eq, hFH]
    have hiffD : x ∈ zGroup Ω ↔ g⁻¹ * x * g ∈ zGroup Ω := by
      constructor
      · intro hx
        have := h.zGroup_normal.conj_mem x hx g⁻¹
        rwa [inv_inv] at this
      · intro hy
        have := h.zGroup_normal.conj_mem _ hy g
        have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rwa [e] at this
    have hiffH : x ∈ H ↔ g⁻¹ * x * g ∈ H₀ := by
      rw [← hg]
      exact mem_conjSub_iff
    unfold deq2Fh
    by_cases hxD : x ∈ zGroup Ω
    · have hgD := hiffD.mp hxD
      by_cases hxH : x ∈ H
      · have hgH := hiffH.mp hxH
        simp [hxD, hxH, hgD, hgH]
      · have hgH : g⁻¹ * x * g ∉ H₀ := fun hh => hxH (hiffH.mpr hh)
        simp [hxD, hxH, hgD, hgH]
    · have hgD : g⁻¹ * x * g ∉ zGroup Ω := fun hh => hxD (hiffD.mpr hh)
      simp [hxD, hgD]

theorem card_pCore_eq : Nat.card (pCore 2 G) = 64 := by
  classical
  obtain ⟨Lf, hLf⟩ : ∃ Lf : G → Subgroup G,
      ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x := by
    have hex : ∀ x : G, ∃ L : Subgroup G,
        x ∈ zGroup Ω → x ≠ 1 → L ∈ Ω ∧ IsUniqueInvolution L x := by
      intro x
      by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
      · rcases h.mem_zGroup_iff.mp hx.1 with h1 | ⟨L, hL, hLx⟩
        · exact absurd h1 hx.2
        · exact ⟨L, fun _ _ => ⟨hL, hLx⟩⟩
      · exact ⟨⊥, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
    choose Lf hLf using hex
    exact ⟨Lf, hLf⟩
  have hsurj : ∀ F ∈ deq2Dual Ω, ∃ q, q ∈ pCore 2 G ∧ deq2Lam Ω Lf q = F := by
    intro F hF
    obtain ⟨q, hq, hqF⟩ := h.deq2_lam_surj hLf hF
    exact ⟨q, hq, hqF⟩
  choose! qF hqF using hsurj
  have hcc : ∀ c : ZMod 2, c + c = 0 := by decide
  have hcinv : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  let Φ : deq2Dual Ω × zGroup Ω → pCore 2 G := fun p =>
    ⟨qF p.1.1 * p.2.1, (pCore 2 G).mul_mem (hqF p.1.1 p.1.2).1 (h.zGroup_le_pCore p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨F, d⟩ ⟨F', d'⟩ hFd
      have hval : qF F.1 * d.1 = qF F'.1 * d'.1 := congrArg Subtype.val hFd
      have e1 : deq2Lam Ω Lf (qF F.1 * d.1) = F.1 := by
        rw [h.deq2_lam_mul hLf (hqF F.1 F.2).1 (h.zGroup_le_pCore d.2),
          (hqF F.1 F.2).2, h.deq2_lam_D hLf d.2, add_zero]
      have e2 : deq2Lam Ω Lf (qF F'.1 * d'.1) = F'.1 := by
        rw [h.deq2_lam_mul hLf (hqF F'.1 F'.2).1 (h.zGroup_le_pCore d'.2),
          (hqF F'.1 F'.2).2, h.deq2_lam_D hLf d'.2, add_zero]
      have hF : F.1 = F'.1 := e1.symm.trans ((congrArg _ hval).trans e2)
      have hq : qF F.1 = qF F'.1 := by rw [hF]
      have hval2 : qF F.1 * d.1 = qF F.1 * d'.1 := hval.trans (by rw [hq])
      exact Prod.ext (Subtype.ext hF) (Subtype.ext (mul_left_cancel hval2))
    · rintro ⟨q, hq⟩
      have hF : deq2Lam Ω Lf q ∈ deq2Dual Ω := h.deq2_lam_mem_dual hLf hq
      have hq'Q : qF (deq2Lam Ω Lf q) ∈ pCore 2 G := (hqF _ hF).1
      have hq'F : deq2Lam Ω Lf (qF (deq2Lam Ω Lf q)) = deq2Lam Ω Lf q := (hqF _ hF).2
      have hinv1 : deq2Lam Ω Lf (qF (deq2Lam Ω Lf q))⁻¹ = deq2Lam Ω Lf (qF (deq2Lam Ω Lf q)) := by
        have h0 := h.deq2_lam_mul hLf ((pCore 2 G).inv_mem hq'Q) hq'Q
        rw [inv_mul_cancel] at h0
        rw [h.deq2_lam_one] at h0
        funext x
        exact hcinv _ _ (congrFun h0.symm x)
      have hdQ : (qF (deq2Lam Ω Lf q))⁻¹ * q ∈ pCore 2 G :=
        (pCore 2 G).mul_mem ((pCore 2 G).inv_mem hq'Q) hq
      have hsum : deq2Lam Ω Lf ((qF (deq2Lam Ω Lf q))⁻¹ * q) = 0 := by
        rw [h.deq2_lam_mul hLf ((pCore 2 G).inv_mem hq'Q) hq, hinv1, hq'F]
        funext x
        rw [Pi.add_apply, hcc, Pi.zero_apply]
      have hdD : (qF (deq2Lam Ω Lf q))⁻¹ * q ∈ zGroup Ω :=
        (h.deq2_lam_eq_zero_iff hLf hdQ).mp hsum
      refine ⟨(⟨deq2Lam Ω Lf q, hF⟩, ⟨_, hdD⟩), ?_⟩
      apply Subtype.ext
      show qF (deq2Lam Ω Lf q) * ((qF (deq2Lam Ω Lf q))⁻¹ * q) = q
      group
  have hcard := Nat.card_congr (Equiv.ofBijective Φ hΦ)
  rw [Nat.card_prod, Nat.card_coe_set_eq, h.deq2_dual_ncard, h.card_zGroup] at hcard
  omega

omit h in
private theorem deq2_zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by
  decide

omit h in
private theorem deq2_zmod2_eq_of_iff : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by
  decide

omit h in
private theorem deq2_zmod2_add_eq_zero : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a + b = 0 := by
  decide

private theorem deq2_flip_twin {q : G} (hq : q ∈ pCore 2 G) {K J : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKz : IsUniqueInvolution K z) (hJz : IsUniqueInvolution J z) :
    flipVal J q = flipVal K q :=
  h.flipVal_eq_of_mem_twinSet hK ⟨hJ, z, hKz, hJz⟩ hq

private theorem deq2_exists_psi {q : G} (hq : q ∈ pCore 2 G) :
    ∃ ψ : G → ZMod 2, ψ 1 = 0 ∧ (∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ψ z = flipVal L q) ∧
      ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, ψ (x * y) = ψ x + ψ y := by
  classical
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : G → ZMod 2, ∀ x : G, ψ x =
      if hx : ∃ L ∈ Ω, IsUniqueInvolution L x then flipVal hx.choose q else 0 :=
    ⟨fun x => if hx : ∃ L ∈ Ω, IsUniqueInvolution L x then flipVal hx.choose q else 0,
      fun _ => rfl⟩
  have hψ1 : ψ 1 = 0 := by
    have hn : ¬ ∃ L ∈ Ω, IsUniqueInvolution L (1 : G) := fun ⟨_, _, hL⟩ => hL.ne_one rfl
    rw [hψdef, dif_neg hn]
  have hval : ∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ψ z = flipVal L q := by
    intro L hL z hz
    have hx : ∃ L ∈ Ω, IsUniqueInvolution L z := ⟨L, hL, hz⟩
    rw [hψdef, dif_pos hx]
    exact (h.deq2_flip_twin hq hx.choose_spec.1 hL hx.choose_spec.2 hz).symm
  refine ⟨ψ, hψ1, hval, ?_⟩
  intro x hx y hy
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, hψ1, zero_add]
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, hψ1, add_zero]
  by_cases hxy : x = y
  · rw [← hxy, h.zGroup_mul_self x hx, hψ1]
    exact (deq2_zmod2_add_self _).symm
  have hxy1 : x * y ≠ 1 := by
    intro e
    apply hxy
    rw [eq_inv_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right (h.zGroup_mul_self x hx)]
  obtain ⟨Kx, hKx, hKxz⟩ : ∃ L ∈ Ω, IsUniqueInvolution L x :=
    (h.mem_zGroup_iff.mp hx).resolve_left hx1
  obtain ⟨Ky, hKy, hKyz⟩ : ∃ L ∈ Ω, IsUniqueInvolution L y :=
    (h.mem_zGroup_iff.mp hy).resolve_left hy1
  obtain ⟨Kxy, hKxy, hKxyz⟩ : ∃ L ∈ Ω, IsUniqueInvolution L (x * y) :=
    (h.mem_zGroup_iff.mp ((zGroup Ω).mul_mem hx hy)).resolve_left hxy1
  rw [hval Kxy hKxy (x * y) hKxyz, hval Kx hKx x hKxz, hval Ky hKy y hKyz]
  exact h.flipVal_add_of_mul hKx hKy hKxy hKxz hKyz hKxyz hxy rfl hq

private theorem deq2_exists_hyp {ψ : G → ZMod 2} (hψ1 : ψ 1 = 0)
    (hadd : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, ψ (x * y) = ψ x + ψ y)
    {t : G} (ht : t ∈ zGroup Ω) (htψ : ψ t ≠ 0) :
    ∃ H : Subgroup G, IsHyp Ω H ∧ ∀ x : G, x ∈ H ↔ x ∈ zGroup Ω ∧ ψ x = 0 := by
  let H : Subgroup G :=
    { carrier := {x | x ∈ zGroup Ω ∧ ψ x = 0}
      mul_mem' := fun {a b} ha hb => ⟨(zGroup Ω).mul_mem ha.1 hb.1, by
        rw [hadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨(zGroup Ω).one_mem, hψ1⟩
      inv_mem' := fun {a} ha => ⟨(zGroup Ω).inv_mem ha.1, by
        have hm := hadd a ha.1 a⁻¹ ((zGroup Ω).inv_mem ha.1)
        rw [mul_inv_cancel, hψ1, ha.2, zero_add] at hm
        exact hm.symm⟩ }
  have hmem : ∀ x : G, x ∈ H ↔ x ∈ zGroup Ω ∧ ψ x = 0 := fun x => Iff.rfl
  have hHset : (H : Set G) = {x | x ∈ zGroup Ω ∧ ψ x = 0} := rfl
  have hDAB : (zGroup Ω : Set G) =
      {x | x ∈ zGroup Ω ∧ ψ x = 0} ∪ {x | x ∈ zGroup Ω ∧ ψ x ≠ 0} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hx
      by_cases h0 : ψ x = 0
      · exact Or.inl ⟨hx, h0⟩
      · exact Or.inr ⟨hx, h0⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint {x : G | x ∈ zGroup Ω ∧ ψ x = 0}
      {x : G | x ∈ zGroup Ω ∧ ψ x ≠ 0} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx.2
  have hBimg : {x : G | x ∈ zGroup Ω ∧ ψ x ≠ 0} =
      (fun x => t * x) '' {x : G | x ∈ zGroup Ω ∧ ψ x = 0} := by
    ext y
    constructor
    · rintro ⟨hyD, hy0⟩
      refine ⟨t * y, ⟨(zGroup Ω).mul_mem ht hyD, ?_⟩, ?_⟩
      · rw [hadd t ht y hyD]
        exact deq2_zmod2_add_eq_zero _ _ htψ hy0
      · show t * (t * y) = y
        rw [← mul_assoc, h.zGroup_mul_self t ht, one_mul]
    · rintro ⟨x, ⟨hxD, hx0⟩, rfl⟩
      refine ⟨(zGroup Ω).mul_mem ht hxD, ?_⟩
      show ψ (t * x) ≠ 0
      rw [hadd t ht x hxD, hx0, add_zero]
      exact htψ
  have hcardB : Set.ncard {x : G | x ∈ zGroup Ω ∧ ψ x ≠ 0} =
      Set.ncard {x : G | x ∈ zGroup Ω ∧ ψ x = 0} := by
    rw [hBimg, Set.ncard_image_of_injective _ (mul_right_injective t)]
  have hD8 : (zGroup Ω : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_zGroup
  rw [hDAB, Set.ncard_union_eq hdisj, hcardB] at hD8
  have hcount : Set.ncard {x : G | x ∈ zGroup Ω ∧ ψ x = 0} = 4 := by omega
  refine ⟨H, ?_, hmem⟩
  unfold IsHyp
  refine ⟨fun x hx => ((hmem x).mp hx).1, ?_⟩
  show Nat.card (H : Set G) = 4
  rw [Nat.card_coe_set_eq, hHset]
  exact hcount

private theorem deq2_flip_normalizer {q : G} (hq : q ∈ pCore 2 G) {ψ : G → ZMod 2}
    (hψ : ∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ψ z = flipVal L q)
    {H : Subgroup G} (hH : ∀ x : G, x ∈ H ↔ x ∈ zGroup Ω ∧ ψ x = 0) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {L : Subgroup G} (hL : L ∈ Ω) :
    flipVal L (g * q * g⁻¹) = flipVal L q := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hL
  have hzD : z ∈ zGroup Ω := deq2_involution_mem h hL hz
  have hM : conjSub g⁻¹ L ∈ Ω := h.hyp.conjInvariant g⁻¹ L hL
  have hMz : IsUniqueInvolution (conjSub g⁻¹ L) (g⁻¹ * z * g) := by
    have hc := hz.conj g⁻¹
    rwa [inv_inv] at hc
  have h1 : flipVal L (g * q * g⁻¹) = flipVal (conjSub g⁻¹ L) q := by
    have hc := h.flipVal_conj hM g hq
    rwa [conjSub_conjSub_inv] at hc
  have hconj : g⁻¹ * z * g ∈ zGroup Ω := by
    have hc := h.zGroup_normal.conj_mem z hzD g⁻¹
    rwa [inv_inv] at hc
  have hiff : g⁻¹ * z * g ∈ H ↔ z ∈ H := by
    have hc := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * z * g)
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at hc
  rw [hH (g⁻¹ * z * g), hH z] at hiff
  have hpsi : ψ (g⁻¹ * z * g) = ψ z := by
    refine deq2_zmod2_eq_of_iff _ _ ⟨fun h0 => ?_, fun h0 => ?_⟩
    · exact (hiff.mp ⟨hconj, h0⟩).2
    · exact (hiff.mpr ⟨hzD, h0⟩).2
  rw [h1, ← hψ _ hM _ hMz, hpsi, hψ L hL z hz]

theorem pCore_mul_self : ∀ q ∈ pCore 2 G, q * q = 1 := by
  intro q hq
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  by_cases hqD : q ∈ zGroup Ω
  · exact h.zGroup_mul_self q hqD
  obtain ⟨ψ, hψ1, hψ, hadd⟩ := h.deq2_exists_psi hq
  obtain ⟨L₀, hL₀, hL₀ne⟩ : ∃ L ∈ Ω, flipVal L q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hqD (h.mem_zGroup_of_flipVal_eq_zero hq hcon)
  obtain ⟨t, ht⟩ := h.exists_isUniqueInvolution hL₀
  have htD : t ∈ zGroup Ω := deq2_involution_mem h hL₀ ht
  have htψ : ψ t ≠ 0 := by
    rw [hψ L₀ hL₀ t ht]
    exact hL₀ne
  obtain ⟨H, hHyp, hH⟩ := h.deq2_exists_hyp hψ1 hadd htD htψ
  have hsD : q * q ∈ zGroup Ω :=
    h.mem_zGroup_of_flipVal_eq_zero ((pCore 2 G).mul_mem hq hq) fun L hL => by
      rw [h.flipVal_mul hL hq hq]
      exact deq2_zmod2_add_self _
  refine h.eq_one_of_forall_normalizer_hyp hHyp hsD ?_
  intro g hg
  have hc : g * q * g⁻¹ ∈ pCore 2 G := hQn.conj_mem q hq g
  have hd : ∀ L ∈ Ω, flipVal L (g * q * g⁻¹ * q⁻¹) = 0 := by
    intro L hL
    have hone : flipVal L 1 = 0 := deq2_flipVal_eq_zero_iff.mpr (conjSub_one L)
    have hinv := h.flipVal_mul hL hq ((pCore 2 G).inv_mem hq)
    rw [mul_inv_cancel, hone] at hinv
    rw [h.flipVal_mul hL hc ((pCore 2 G).inv_mem hq),
      h.deq2_flip_normalizer hq hψ hH hg hL]
    exact hinv.symm
  have hdD : g * q * g⁻¹ * q⁻¹ ∈ zGroup Ω :=
    h.mem_zGroup_of_flipVal_eq_zero ((pCore 2 G).mul_mem hc ((pCore 2 G).inv_mem hq)) hd
  have hfinal : ∀ d ∈ zGroup Ω, g * q * g⁻¹ = d * q → g * (q * q) * g⁻¹ = q * q := by
    intro d hdD' hcd
    have hqd : q * d = d * q :=
      (Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) d hdD').symm
    calc g * (q * q) * g⁻¹ = (g * q * g⁻¹) * (g * q * g⁻¹) := by group
      _ = (d * q) * (d * q) := by rw [hcd]
      _ = d * (q * d) * q := by group
      _ = d * (d * q) * q := by rw [hqd]
      _ = (d * d) * (q * q) := by group
      _ = q * q := by rw [h.zGroup_mul_self d hdD', one_mul]
  exact hfinal _ hdD (by group)

theorem pCore_comm : ∀ a ∈ pCore 2 G, ∀ b ∈ pCore 2 G, a * b = b * a := by
  intro a ha b hb
  have hab : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (h.pCore_mul_self (a * b) ((pCore 2 G).mul_mem ha hb))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
      rw [inv_eq_of_mul_eq_one_right (h.pCore_mul_self b hb),
        inv_eq_of_mul_eq_one_right (h.pCore_mul_self a ha)]

omit h in
private theorem deq2_exists_two_ne_one {H : Subgroup G} (hH : Nat.card H = 4) :
    ∃ x₁ ∈ H, ∃ x₂ ∈ H, x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ≠ x₂ := by
  have h4 : (H : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hH
  have h2 : 2 < (H : Set G).ncard := by
    rw [h4]
    norm_num
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp h2
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨b, hb, c, hc, fun e => hab e.symm, fun e => hac e.symm, hbc⟩
  by_cases hb1 : b = 1
  · subst hb1
    exact ⟨a, ha, c, hc, ha1, fun e => hbc e.symm, hac⟩
  exact ⟨a, ha, b, hb, ha1, hb1, hab⟩

private theorem deq2_flipVal_zGroup {K : Subgroup G} (hK : K ∈ Ω) {d : G}
    (hd : d ∈ zGroup Ω) : flipVal K d = 0 :=
  deq2_flipVal_eq_zero_iff.mpr (mem_normalizer_iff_conjSub_eq.mp (h.dNorm K hK hd))

private theorem deq2_dComm_pCore_zGroup {q : G} (hq : q ∈ pCore 2 G) {d : G}
    (hd : d ∈ zGroup Ω) : dComm q d = 1 :=
  dComm_eq_one_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) d hd).symm)

omit h in
private theorem deq2_dComm_eq_one_of_zpowers {L : Subgroup G} {z : G}
    (hz : IsUniqueInvolution L z) {w : G} (hw : w = 1 ∨ w = z) {k : G} (hk : k ∈ L) :
    dComm w k = 1 := by
  rcases hw with hw | hw
  · rw [hw]
    simp [dComm]
  · rw [hw]
    exact deq2_dComm_involution_one hz hk

omit h in
private theorem deq2_dComm_one_left (k : G) : dComm (1 : G) k = 1 := by
  simp [dComm]

omit h in
private theorem deq2_mul_self_eq_one {z c : G} (hz : z * z = 1) (hc : c = 1 ∨ c = z) :
    c * c = 1 := by
  rcases hc with hc | hc
  · rw [hc, one_mul]
  · rw [hc]
    exact hz

private theorem deq2_dComm_mul_of_zpowers {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {w e : G} (hw : w ∈ Subgroup.zpowers z) (he : e ∈ zGroup Ω)
    {k : G} (hk : k ∈ K) : dComm (w * e) k = dComm e k := by
  have hw1 := deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one hw
  have hwN : w ∈ Subgroup.normalizer (K : Set G) := by
    rcases hw1 with hw1 | hw1
    · rw [hw1]
      exact Subgroup.one_mem _
    · rw [hw1]
      exact h.dNorm K hK (deq2_involution_mem h hK hz)
  have hc : dComm e k = 1 ∨ dComm e k = z :=
    deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one (h.dComm_mem_zpowers hK hz he hk)
  rw [dComm_mul_left hz hwN hc, deq2_dComm_eq_one_of_zpowers hz hw1 hk, mul_one]

private theorem deq2_mem_zpowers_of_comm {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {w : G} (hw : w ∈ zGroup Ω)
    (hc : ∀ k ∈ K, k * w = w * k) : w ∈ Subgroup.zpowers z := by
  have hdd : ∀ k ∈ K, dComm w k = dComm 1 k := by
    intro k hk
    rw [dComm_eq_one_iff.mpr (hc k hk).symm, deq2_dComm_one_left]
  have key := h.eq_of_dComm_eq hK hz hw (zGroup Ω).one_mem hdd
  rw [one_mul] at key
  have key' := (Subgroup.zpowers z).inv_mem key
  rwa [inv_inv] at key'

omit h in
private theorem deq2_inv_comm {K : Subgroup G} {y : G} (hy : ∀ k ∈ K, k * y = y * k) :
    ∀ k ∈ K, k * y⁻¹ = y⁻¹ * k := by
  intro k hk
  have e := hy k hk
  calc k * y⁻¹ = y⁻¹ * (y * k) * y⁻¹ := by group
    _ = y⁻¹ * (k * y) * y⁻¹ := by rw [e]
    _ = y⁻¹ * k := by group

omit h in
private theorem deq2_comm_conjSub {y g : G} (hg : g * y = y * g) {K : Subgroup G}
    (hK : ∀ k ∈ K, k * y = y * k) : ∀ x ∈ conjSub g K, x * y = y * x := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have hgi : g⁻¹ * y = y * g⁻¹ := by
    calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hg]
      _ = y * g⁻¹ := by group
  have hk := hK _ hx
  calc x * y = g * (g⁻¹ * x * g) * g⁻¹ * y := by group
    _ = g * (g⁻¹ * x * g) * (g⁻¹ * y) := by group
    _ = g * (g⁻¹ * x * g) * (y * g⁻¹) := by rw [hgi]
    _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hk]
    _ = (g * y) * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = (y * g) * (g⁻¹ * x * g) * g⁻¹ := by rw [hg]
    _ = y * x := by group

omit h in
private theorem deq2_normalizer_of_comm {L : Subgroup G} {w : G}
    (hw : ∀ x ∈ L, x * w = w * x) : w ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have e : w * g * w⁻¹ = g := by
      rw [(hw g hg).symm]
      group
    rw [e]
    exact hg
  · intro hg
    have hl := hw _ hg
    have e : g = w * g * w⁻¹ := by
      calc g = w⁻¹ * (w * g * w⁻¹) * w := by group
        _ = w⁻¹ * ((w * g * w⁻¹) * w) := by group
        _ = w⁻¹ * (w * (w * g * w⁻¹)) := by rw [hl]
        _ = w * g * w⁻¹ := by group
    rw [e]
    exact hg

omit h in
private theorem deq2_flipVal_of_comm {H L : Subgroup G} (hL : L ∈ omegaHyp Ω H) {w : G}
    (hw : ∀ g ∈ pSpan (omegaHyp Ω H), g * w = w * g) : flipVal L w = 0 :=
  deq2_flipVal_eq_zero_iff.mpr (mem_normalizer_iff_conjSub_eq.mp
    (deq2_normalizer_of_comm fun x hx => hw x (le_pSpan hL hx)))

private theorem deq2_twin_commute {K : Subgroup G} (hK : K ∈ Ω) {y : G} (hyQ : y ∈ pCore 2 G)
    (hyK : ∀ k ∈ K, k * y = y * k) {J : Subgroup G} (hJ : J ∈ twinSet Ω K) :
    ∀ x ∈ J, x * y = y * x := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨q', hq', hf'⟩ := h.exists_flip hK
  have hKS : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hJ1 : conjSub q' K ∈ twinSet Ω K := h.conjSub_mem_twinSet hq' hK
  have hne : conjSub q' K ≠ K := deq2_flipVal_eq_one_iff.mp hf'
  have hS := deq2_twinSet_eq_pair (h.twin2 K hK) hKS hJ1 hne
  rw [hS] at hJ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
  rcases hJ with hJ | hJ
  · rw [hJ]
    exact hyK
  · rw [hJ]
    exact deq2_comm_conjSub (h.pCore_comm q' hq' y hyQ) hyK

private theorem deq2_dual_eq_fh_of_vanish {H : Subgroup G} (hH : IsHyp Ω H) {F : G → ZMod 2}
    (hF : F ∈ deq2Dual Ω) (hF0 : F ≠ 0) (hFH : ∀ x ∈ H, F x = 0) : F = deq2Fh Ω H := by
  obtain ⟨H', hH', hFH'⟩ := h.deq2_dual_eq_fh hF hF0
  have hle : H ≤ H' := by
    intro x hx
    by_contra hxH'
    have h1 := hFH x hx
    rw [hFH'] at h1
    have h2 : deq2Fh Ω H' x = 1 := by
      unfold deq2Fh
      rw [if_pos ⟨hH.1 hx, hxH'⟩]
    rw [h2] at h1
    exact one_ne_zero h1
  have heq : H = H' := Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hH'.2.trans hH.2.symm))
  subst heq
  exact hFH'

private theorem deq2_lam_inv {Lf : G → Subgroup G}
    (hLf : ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x)
    {q : G} (hq : q ∈ pCore 2 G) : deq2Lam Ω Lf q⁻¹ = deq2Lam Ω Lf q := by
  have hcinv : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have h0 := h.deq2_lam_mul hLf hq ((pCore 2 G).inv_mem hq)
  rw [mul_inv_cancel, h.deq2_lam_one] at h0
  funext x
  have h1 := congrFun h0.symm x
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  exact (hcinv _ _ h1).symm

theorem exists_unique_yElt {H : Subgroup G} (hH : IsHyp Ω H) :
    ∃ y : G, y ∈ pCore 2 G ∧ y ∉ zGroup Ω ∧
      (∀ g ∈ pSpan (omegaHyp Ω H), g * y = y * g) ∧
      ∀ y' ∈ pCore 2 G, (∀ g ∈ pSpan (omegaHyp Ω H), g * y' = y' * g) → y' = 1 ∨ y' = y := by
  have hcc : ∀ c : ZMod 2, c + c = 0 := by decide
  obtain ⟨x₁, hx₁H, x₂, hx₂H, hx₁1, hx₂1, hx₁₂⟩ := deq2_exists_two_ne_one hH.2
  have hx₁D : x₁ ∈ zGroup Ω := hH.1 hx₁H
  have hx₂D : x₂ ∈ zGroup Ω := hH.1 hx₂H
  obtain ⟨H₀, hH₀, hH₀char⟩ := h.deq2_hyp_pair hx₁D hx₂D hx₁1 hx₂1 hx₁₂
  have hHeq : H₀ = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq (hH.2.trans hH₀.2.symm))
    intro g hg
    rcases (hH₀char g).mp hg with h1 | h1 | h1 | h1
    · rw [h1]
      exact H.one_mem
    · rw [h1]
      exact hx₁H
    · rw [h1]
      exact hx₂H
    · rw [h1]
      exact H.mul_mem hx₁H hx₂H
  have hHchar : ∀ g : G, g ∈ H ↔ g = 1 ∨ g = x₁ ∨ g = x₂ ∨ g = x₁ * x₂ := by
    intro g
    rw [← hHeq]
    exact hH₀char g
  obtain ⟨Lf, hLf⟩ : ∃ Lf : G → Subgroup G,
      ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x := by
    have hex : ∀ x : G, ∃ L : Subgroup G,
        x ∈ zGroup Ω → x ≠ 1 → L ∈ Ω ∧ IsUniqueInvolution L x := by
      intro x
      by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
      · rcases h.mem_zGroup_iff.mp hx.1 with h1 | ⟨L, hL, hLx⟩
        · exact absurd h1 hx.2
        · exact ⟨L, fun _ _ => ⟨hL, hLx⟩⟩
      · exact ⟨⊥, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
    choose Lf hLf using hex
    exact ⟨Lf, hLf⟩
  obtain ⟨q₁, hq₁, hq₁F⟩ := h.deq2_lam_surj hLf (h.deq2_fh_mem_dual hH)
  have hflip : ∀ x ∈ zGroup Ω, x ≠ 1 → flipVal (Lf x) q₁ = deq2Fh Ω H x := by
    intro x hx hx1
    have e := congrFun hq₁F x
    unfold deq2Lam at e
    rwa [if_pos ⟨hx, hx1⟩] at e
  have hfl₁ : flipVal (Lf x₁) q₁ = 0 := by
    rw [hflip x₁ hx₁D hx₁1]
    simp [deq2Fh, hx₁H]
  have hfl₂ : flipVal (Lf x₂) q₁ = 0 := by
    rw [hflip x₂ hx₂D hx₂1]
    simp [deq2Fh, hx₂H]
  have hq₁D : q₁ ∉ zGroup Ω := by
    intro hD
    obtain ⟨x, hxD, hxH⟩ : ∃ x ∈ zGroup Ω, x ∉ H := by
      by_contra hcon
      push_neg at hcon
      have hc := Subgroup.card_le_of_le (show zGroup Ω ≤ H from fun x hx => hcon x hx)
      rw [h.card_zGroup, hH.2] at hc
      omega
    have h0 : deq2Lam Ω Lf q₁ = 0 := (h.deq2_lam_eq_zero_iff hLf hq₁).mpr hD
    have e1 : deq2Fh Ω H x = 1 := by simp [deq2Fh, hxD, hxH]
    have e2 : deq2Fh Ω H x = 0 := by
      rw [← hq₁F]
      exact congrFun h0 x
    rw [e1] at e2
    exact one_ne_zero e2
  obtain ⟨K₁, hK₁Ω, hz₁, hfl₁'⟩ : ∃ K, K ∈ Ω ∧ IsUniqueInvolution K x₁ ∧ flipVal K q₁ = 0 :=
    ⟨Lf x₁, (hLf x₁ hx₁D hx₁1).1, (hLf x₁ hx₁D hx₁1).2, hfl₁⟩
  obtain ⟨K₂, hK₂Ω, hz₂, hfl₂'⟩ : ∃ K, K ∈ Ω ∧ IsUniqueInvolution K x₂ ∧ flipVal K q₁ = 0 :=
    ⟨Lf x₂, (hLf x₂ hx₂D hx₂1).1, (hLf x₂ hx₂D hx₂1).2, hfl₂⟩
  have hK₁H : K₁ ∈ omegaHyp Ω H := ⟨hK₁Ω, x₁, hx₁H, hz₁⟩
  have hK₂H : K₂ ∈ omegaHyp Ω H := ⟨hK₂Ω, x₂, hx₂H, hz₂⟩
  have hq₁N : q₁ ∈ Subgroup.normalizer (K₁ : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (deq2_flipVal_eq_zero_iff.mp hfl₁')
  have hdcq₁ : ∀ k ∈ K₁, dComm q₁ k ∈ Subgroup.zpowers x₁ := fun k hk =>
    h.deq2_dComm_pCore_mem hq₁ hK₁Ω hfl₁' hz₁ hk
  let f₁ : K₁ →* Subgroup.zpowers x₁ := MonoidHom.mk'
    (fun k : K₁ => (⟨dComm q₁ (k : G), hdcq₁ (k : G) k.2⟩ : Subgroup.zpowers x₁)) (by
      intro a b
      apply Subtype.ext
      show dComm q₁ ((a : G) * (b : G)) = dComm q₁ (a : G) * dComm q₁ (b : G)
      exact dComm_mul_right hz₁ a.2 b.2 hq₁N
        (deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one (hdcq₁ (b : G) b.2)))
  have hf₁ : f₁ ⟨x₁, hz₁.mem⟩ = 1 := by
    apply Subtype.ext
    show dComm q₁ x₁ = 1
    exact h.deq2_dComm_pCore_zGroup hq₁ hx₁D
  obtain ⟨d₁, hd₁D, hd₁⟩ := h.exists_dComm_eq_hom hK₁Ω hz₁ f₁ hf₁
  have hd₁' : ∀ k ∈ K₁, dComm d₁ k = dComm q₁ k := fun k hk => hd₁ ⟨k, hk⟩
  have hd₁Q : d₁ ∈ pCore 2 G := h.zGroup_le_pCore hd₁D
  obtain ⟨q, hqQ, hqD, hfq₁, hfq₂, hqK₁⟩ : ∃ q : G, q ∈ pCore 2 G ∧ q ∉ zGroup Ω ∧
      flipVal K₁ q = 0 ∧ flipVal K₂ q = 0 ∧ ∀ k ∈ K₁, dComm q k = 1 := by
    refine ⟨q₁ * d₁, (pCore 2 G).mul_mem hq₁ hd₁Q, ?_, ?_, ?_, ?_⟩
    · intro hm
      apply hq₁D
      simpa using (zGroup Ω).mul_mem hm ((zGroup Ω).inv_mem hd₁D)
    · rw [h.flipVal_mul hK₁Ω hq₁ hd₁Q, h.deq2_flipVal_zGroup hK₁Ω hd₁D, hfl₁', add_zero]
    · rw [h.flipVal_mul hK₂Ω hq₁ hd₁Q, h.deq2_flipVal_zGroup hK₂Ω hd₁D, hfl₂', add_zero]
    · intro k hk
      have e1 := dComm_mul_left hz₁ hq₁N
        (deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one
          (h.dComm_mem_zpowers hK₁Ω hz₁ hd₁D hk))
      rw [e1, hd₁' k hk]
      exact deq2_mul_self_eq_one hz₁.sq
        (deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one (hdcq₁ k hk))
  have hqN₁ : q ∈ Subgroup.normalizer (K₁ : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (deq2_flipVal_eq_zero_iff.mp hfq₁)
  have hqN₂ : q ∈ Subgroup.normalizer (K₂ : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (deq2_flipVal_eq_zero_iff.mp hfq₂)
  have hnot : K₂ ∉ twinSet Ω K₁ := by
    rintro ⟨-, z, hKz, hKz₂⟩
    exact hx₁₂ ((hz₁.eq hKz).trans (hz₂.eq hKz₂).symm)
  obtain ⟨hcardA, -, hnormA⟩ :=
    h.card_inf_centralizer_of_not_mem_twinSet hK₁Ω hK₂Ω hnot hz₁
  have hA : ∃ a ∈ K₂ ⊓ Subgroup.centralizer ({x₁} : Set G), a ∉ Subgroup.zpowers x₂ := by
    by_contra hcon
    push_neg at hcon
    have hle : K₂ ⊓ Subgroup.centralizer ({x₁} : Set G) ≤ Subgroup.zpowers x₂ :=
      fun a ha => hcon a ha
    have hc := Subgroup.card_le_of_le hle
    rw [hcardA, card_zpowers_of_involution hz₂.sq hz₂.ne_one] at hc
    omega
  obtain ⟨a, haA, haz⟩ := hA
  have ha2 : a ∈ K₂ := (Subgroup.mem_inf.mp haA).1
  have hax₁ : a * x₁ = x₁ * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp haA).2
  have hanorm : a ∈ Subgroup.normalizer (K₁ : Set G) :=
    hnormA K₁ ⟨hK₁Ω, x₁, hz₁, hz₁⟩ haA
  have hid : ∀ k ∈ K₁, dComm q a * (a * k * a⁻¹) = (a * k * a⁻¹) * dComm q a := by
    intro k hk
    have hm : a * k * a⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hanorm k).mp hk
    have hqk : q * k = k * q := dComm_eq_one_iff.mp (hqK₁ k hk)
    have hqm : q * (a * k * a⁻¹) = (a * k * a⁻¹) * q := dComm_eq_one_iff.mp (hqK₁ _ hm)
    have hqk' : q⁻¹ * k * q = k := by
      rw [mul_assoc, ← hqk, inv_mul_cancel_left]
    have hbk : (q * a * q⁻¹) * k * (q * a * q⁻¹)⁻¹ = a * k * a⁻¹ := by
      calc (q * a * q⁻¹) * k * (q * a * q⁻¹)⁻¹
          = q * a * (q⁻¹ * k * q) * a⁻¹ * q⁻¹ := by group
        _ = q * a * k * a⁻¹ * q⁻¹ := by rw [hqk']
        _ = q * (a * k * a⁻¹) * q⁻¹ := by group
        _ = (a * k * a⁻¹) * q * q⁻¹ := by rw [hqm]
        _ = a * k * a⁻¹ := by group
    have hbk' : (q * a * q⁻¹) * k = (a * k * a⁻¹) * (q * a * q⁻¹) :=
      mul_inv_eq_iff_eq_mul.mp hbk
    calc dComm q a * (a * k * a⁻¹) = ((q * a * q⁻¹) * k) * a⁻¹ := by
          unfold dComm
          group
      _ = ((a * k * a⁻¹) * (q * a * q⁻¹)) * a⁻¹ := by rw [hbk']
      _ = (a * k * a⁻¹) * dComm q a := by
          unfold dComm
          group
  have hεK₁ : ∀ m ∈ K₁, dComm q a * m = m * dComm q a := by
    intro m hm
    have hk : a⁻¹ * m * a ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp hanorm (a⁻¹ * m * a)).mpr (by
        rw [show a * (a⁻¹ * m * a) * a⁻¹ = m by group]
        exact hm)
    have h1 := hid (a⁻¹ * m * a) hk
    rwa [show a * (a⁻¹ * m * a) * a⁻¹ = m by group] at h1
  have hε1 : dComm q a = 1 := by
    have hεmem : dComm q a ∈ Subgroup.zpowers x₂ :=
      h.deq2_dComm_pCore_mem hqQ hK₂Ω hfq₂ hz₂ ha2
    rcases deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one hεmem with h1 | h1
    · exact h1
    · exfalso
      have hc : ∀ m ∈ K₁, m * x₂ = x₂ * m := fun m hm => by
        have h2 := hεK₁ m hm
        rw [h1] at h2
        exact h2.symm
      rcases deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one
          (h.deq2_mem_zpowers_of_comm hK₁Ω hz₁ hx₂D hc) with h2 | h2
      · exact hx₂1 h2
      · exact hx₁₂ h2.symm
  have hdcq₂ : ∀ k ∈ K₂, dComm q k ∈ Subgroup.zpowers x₂ := fun k hk =>
    h.deq2_dComm_pCore_mem hqQ hK₂Ω hfq₂ hz₂ hk
  let f₂ : K₂ →* Subgroup.zpowers x₂ := MonoidHom.mk'
    (fun k : K₂ => (⟨dComm q (k : G), hdcq₂ (k : G) k.2⟩ : Subgroup.zpowers x₂)) (by
      intro a' b'
      apply Subtype.ext
      show dComm q ((a' : G) * (b' : G)) = dComm q (a' : G) * dComm q (b' : G)
      exact dComm_mul_right hz₂ a'.2 b'.2 hqN₂
        (deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one (hdcq₂ (b' : G) b'.2)))
  have hf₂ : f₂ ⟨x₂, hz₂.mem⟩ = 1 := by
    apply Subtype.ext
    show dComm q x₂ = 1
    exact h.deq2_dComm_pCore_zGroup hqQ hx₂D
  obtain ⟨d₂, hd₂D, hd₂⟩ := h.exists_dComm_eq_hom hK₂Ω hz₂ f₂ hf₂
  have hd₂' : ∀ k ∈ K₂, dComm d₂ k = dComm q k := fun k hk => hd₂ ⟨k, hk⟩
  have hd₂a : d₂ * a = a * d₂ := dComm_eq_one_iff.mp (by rw [hd₂' a ha2]; exact hε1)
  have hax₂ : a * x₂ = x₂ * a :=
    mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem hz₂ ha2 (Or.inr rfl : x₂ = 1 ∨ x₂ = x₂))
  have hx₁₂a : x₁ * x₂ * a = a * (x₁ * x₂) := by
    calc x₁ * x₂ * a = x₁ * (x₂ * a) := mul_assoc _ _ _
      _ = x₁ * (a * x₂) := by rw [← hax₂]
      _ = (x₁ * a) * x₂ := (mul_assoc _ _ _).symm
      _ = (a * x₁) * x₂ := by rw [← hax₁]
      _ = a * (x₁ * x₂) := mul_assoc _ _ _
  have hcardS := h.card_zGroup_inf_centralizer hK₂Ω hz₂ ha2 haz
  have hHS : H ≤ zGroup Ω ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rcases (hHchar g).mp hg with h1 | h1 | h1 | h1
    · rw [h1]
      exact ⟨(zGroup Ω).one_mem, Subgroup.one_mem _⟩
    · rw [h1]
      exact ⟨hx₁D, Subgroup.mem_centralizer_singleton_iff.mpr hax₁.symm⟩
    · rw [h1]
      exact ⟨hx₂D, Subgroup.mem_centralizer_singleton_iff.mpr hax₂.symm⟩
    · rw [h1]
      exact ⟨(zGroup Ω).mul_mem hx₁D hx₂D, Subgroup.mem_centralizer_singleton_iff.mpr hx₁₂a⟩
  have hHS_eq : H = zGroup Ω ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hHS (le_of_eq (hcardS.trans hH.2.symm))
  have hd₂H : d₂ ∈ H := by
    rw [hHS_eq]
    exact ⟨hd₂D, Subgroup.mem_centralizer_singleton_iff.mpr hd₂a⟩
  obtain ⟨e, he, hed⟩ : ∃ e : G, (e = 1 ∨ e = x₁) ∧ d₂ * e⁻¹ ∈ Subgroup.zpowers x₂ := by
    rcases (hHchar d₂).mp hd₂H with h1 | h1 | h1 | h1
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h1, inv_one, mul_one]
      exact Subgroup.one_mem _
    · refine ⟨x₁, Or.inr rfl, ?_⟩
      rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h1, inv_one, mul_one]
      exact Subgroup.mem_zpowers x₂
    · refine ⟨x₁, Or.inr rfl, ?_⟩
      rw [h1, h.zGroup_comm x₁ hx₁D x₂ hx₂D, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers x₂
  have heD : e ∈ zGroup Ω := by
    rcases he with h1 | h1
    · rw [h1]
      exact (zGroup Ω).one_mem
    · rw [h1]
      exact hx₁D
  have hE : ∀ k ∈ K₂, dComm e k = dComm q k := by
    intro k hk
    have h1 := h.deq2_dComm_mul_of_zpowers hK₂Ω hz₂ hed heD hk
    rw [inv_mul_cancel_right, hd₂' k hk] at h1
    exact h1.symm
  have hyK₁0 : ∀ k ∈ K₁, k * (q * e) = (q * e) * k := by
    intro k hk
    have e1 : dComm (q * e) k = dComm e k * dComm q k :=
      dComm_mul_left hz₁ hqN₁ (Or.inl (deq2_dComm_eq_one_of_zpowers hz₁ he hk))
    rw [deq2_dComm_eq_one_of_zpowers hz₁ he hk, hqK₁ k hk, one_mul] at e1
    exact (dComm_eq_one_iff.mp e1).symm
  have hyK₂0 : ∀ k ∈ K₂, k * (q * e) = (q * e) * k := by
    intro k hk
    have e1 : dComm (q * e) k = dComm e k * dComm q k :=
      dComm_mul_left hz₂ hqN₂ (deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one
        (h.dComm_mem_zpowers hK₂Ω hz₂ heD hk))
    have e2 : dComm (q * e) k = 1 := by
      rw [e1, hE k hk]
      exact deq2_mul_self_eq_one hz₂.sq
        (deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one (hdcq₂ k hk))
    exact (dComm_eq_one_iff.mp e2).symm
  have hyQ0 : q * e ∈ pCore 2 G := (pCore 2 G).mul_mem hqQ (h.zGroup_le_pCore heD)
  have hyD0 : q * e ∉ zGroup Ω := by
    intro hm
    apply hqD
    simpa using (zGroup Ω).mul_mem hm ((zGroup Ω).inv_mem heD)
  obtain ⟨y, hyQ, hyD, hyK₁, hyK₂⟩ : ∃ y : G, y ∈ pCore 2 G ∧ y ∉ zGroup Ω ∧
      (∀ k ∈ K₁, k * y = y * k) ∧ (∀ k ∈ K₂, k * y = y * k) :=
    ⟨q * e, hyQ0, hyD0, hyK₁0, hyK₂0⟩
  obtain ⟨k₀, hk₀K₁, M, hMΩ, hMeq, hMinv⟩ := h.exists_star hK₁Ω hK₂Ω hz₁ hz₂ hx₁₂
  have hyM : ∀ m ∈ M, m * y = y * m := by
    rw [hMeq]
    exact deq2_comm_conjSub (hyK₁ k₀ hk₀K₁) hyK₂
  have hyc : ∀ L ∈ omegaHyp Ω H, ∀ x ∈ L, x * y = y * x := by
    rintro L ⟨hLΩ, u, huH, hLu⟩ x hx
    rcases (hHchar u).mp huH with h1 | h1 | h1 | h1
    · rw [h1] at hLu
      exact absurd rfl hLu.ne_one
    · rw [h1] at hLu
      exact h.deq2_twin_commute hK₁Ω hyQ hyK₁ ⟨hLΩ, x₁, hz₁, hLu⟩ x hx
    · rw [h1] at hLu
      exact h.deq2_twin_commute hK₂Ω hyQ hyK₂ ⟨hLΩ, x₂, hz₂, hLu⟩ x hx
    · rw [h1] at hLu
      exact h.deq2_twin_commute hMΩ hyQ hyM ⟨hLΩ, x₁ * x₂, hMinv, hLu⟩ x hx
  have hyc' : ∀ g ∈ pSpan (omegaHyp Ω H), g * y = y * g := by
    have hpS : pSpan (omegaHyp Ω H) ≤ Subgroup.centralizer ({y} : Set G) := by
      apply pSpan_le
      intro L hL x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hyc L hL x hx)
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hpS hg)
  refine ⟨y, hyQ, hyD, hyc', ?_⟩
  intro y' hy'Q hy'c
  have hvan : ∀ w ∈ pCore 2 G, (∀ g ∈ pSpan (omegaHyp Ω H), g * w = w * g) →
      ∀ x ∈ H, deq2Lam Ω Lf w x = 0 := by
    intro w _ hwc x hx
    by_cases hx1 : x = 1
    · subst hx1
      simp [deq2Lam]
    · have hxD := hH.1 hx
      have hLx : Lf x ∈ omegaHyp Ω H :=
        ⟨(hLf x hxD hx1).1, x, hx, (hLf x hxD hx1).2⟩
      unfold deq2Lam
      rw [if_pos ⟨hxD, hx1⟩]
      exact deq2_flipVal_of_comm hLx hwc
  have hyvan : ∀ x ∈ H, deq2Lam Ω Lf y x = 0 := hvan y hyQ hyc'
  have hy'van : ∀ x ∈ H, deq2Lam Ω Lf y' x = 0 := hvan y' hy'Q hy'c
  have hy'K₁ : ∀ k ∈ K₁, k * y' = y' * k := fun k hk => hy'c k (le_pSpan hK₁H hk)
  have hy'K₂ : ∀ k ∈ K₂, k * y' = y' * k := fun k hk => hy'c k (le_pSpan hK₂H hk)
  by_cases hF0 : deq2Lam Ω Lf y' = 0
  ·
    have hy'D : y' ∈ zGroup Ω := (h.deq2_lam_eq_zero_iff hLf hy'Q).mp hF0
    rcases deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one
        (h.deq2_mem_zpowers_of_comm hK₁Ω hz₁ hy'D hy'K₁) with e1 | e1
    · exact Or.inl e1
    · rcases deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one
          (h.deq2_mem_zpowers_of_comm hK₂Ω hz₂ hy'D hy'K₂) with e2 | e2
      · exact Or.inl e2
      · exact (hx₁₂ (e1.symm.trans e2)).elim
  ·
    have hyF0 : deq2Lam Ω Lf y ≠ 0 := fun h0 => hyD ((h.deq2_lam_eq_zero_iff hLf hyQ).mp h0)
    have hFy : deq2Lam Ω Lf y' = deq2Fh Ω H :=
      h.deq2_dual_eq_fh_of_vanish hH (h.deq2_lam_mem_dual hLf hy'Q) hF0 hy'van
    have hFy2 : deq2Lam Ω Lf y = deq2Fh Ω H :=
      h.deq2_dual_eq_fh_of_vanish hH (h.deq2_lam_mem_dual hLf hyQ) hyF0 hyvan
    have hwQ : y' * y⁻¹ ∈ pCore 2 G := (pCore 2 G).mul_mem hy'Q ((pCore 2 G).inv_mem hyQ)
    have hwD : y' * y⁻¹ ∈ zGroup Ω := by
      rw [← h.deq2_lam_eq_zero_iff hLf hwQ,
        h.deq2_lam_mul hLf hy'Q ((pCore 2 G).inv_mem hyQ), h.deq2_lam_inv hLf hyQ, hFy, hFy2]
      funext x
      rw [Pi.add_apply, Pi.zero_apply]
      exact hcc _
    have hwK₁ : ∀ k ∈ K₁, k * (y' * y⁻¹) = (y' * y⁻¹) * k := fun k hk => by
      calc k * (y' * y⁻¹) = (k * y') * y⁻¹ := (mul_assoc _ _ _).symm
        _ = (y' * k) * y⁻¹ := by rw [hy'K₁ k hk]
        _ = y' * (k * y⁻¹) := mul_assoc _ _ _
        _ = y' * (y⁻¹ * k) := by rw [deq2_inv_comm hyK₁ k hk]
        _ = (y' * y⁻¹) * k := (mul_assoc _ _ _).symm
    have hwK₂ : ∀ k ∈ K₂, k * (y' * y⁻¹) = (y' * y⁻¹) * k := fun k hk => by
      calc k * (y' * y⁻¹) = (k * y') * y⁻¹ := (mul_assoc _ _ _).symm
        _ = (y' * k) * y⁻¹ := by rw [hy'K₂ k hk]
        _ = y' * (k * y⁻¹) := mul_assoc _ _ _
        _ = y' * (y⁻¹ * k) := by rw [deq2_inv_comm hyK₂ k hk]
        _ = (y' * y⁻¹) * k := (mul_assoc _ _ _).symm
    have hwI₁ : y' * y⁻¹ ∈ Subgroup.zpowers x₁ :=
      h.deq2_mem_zpowers_of_comm hK₁Ω hz₁ hwD hwK₁
    have hwI₂ : y' * y⁻¹ ∈ Subgroup.zpowers x₂ :=
      h.deq2_mem_zpowers_of_comm hK₂Ω hz₂ hwD hwK₂
    have hw1 : y' * y⁻¹ = 1 := by
      rcases deq2_eq_one_or_eq_of_mem_zpowers hz₁.sq hz₁.ne_one hwI₁ with e1 | e1
      · exact e1
      · rcases deq2_eq_one_or_eq_of_mem_zpowers hz₂.sq hz₂.ne_one hwI₂ with e2 | e2
        · exact e2
        · exact (hx₁₂ (e1.symm.trans e2)).elim
    exact Or.inr (mul_inv_eq_one.mp hw1)

open Classical in
@[expose] noncomputable def yElt (H : Subgroup G) : G :=
  if hH : IsHyp Ω H then (h.exists_unique_yElt hH).choose else 1

private theorem deq2_exists_Lf : ∃ Lf : G → Subgroup G,
    ∀ x, x ∈ zGroup Ω → x ≠ 1 → Lf x ∈ Ω ∧ IsUniqueInvolution (Lf x) x := by
  have hex : ∀ x : G, ∃ L : Subgroup G,
      x ∈ zGroup Ω → x ≠ 1 → L ∈ Ω ∧ IsUniqueInvolution L x := by
    intro x
    by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
    · rcases h.mem_zGroup_iff.mp hx.1 with h1 | ⟨L, hL, hLx⟩
      · exact absurd h1 hx.2
      · exact ⟨L, fun _ _ => ⟨hL, hLx⟩⟩
    · exact ⟨⊥, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
  choose Lf hLf using hex
  exact ⟨Lf, hLf⟩

private theorem deq2_flip_zero_of_centralizes {H : Subgroup G} {y : G}
    (hyc : ∀ g ∈ pSpan (omegaHyp Ω H), g * y = y * g) {L : Subgroup G} (hL : L ∈ Ω) {u : G}
    (hu : u ∈ H) (hLu : IsUniqueInvolution L u) : flipVal L y = 0 := by
  apply deq2_flipVal_eq_zero_iff.mpr
  rw [← mem_normalizer_iff_conjSub_eq]
  have hLle : L ≤ pSpan (omegaHyp Ω H) := le_pSpan ⟨hL, u, hu, hLu⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [← hyc k (hLle hk), mul_inv_cancel_right]
    exact hk
  · intro hk
    have hm : y * k * y⁻¹ ∈ L := hk
    have hmy := hyc _ (hLle hm)
    have hkm : k = y * k * y⁻¹ := by
      calc k = y⁻¹ * (y * k * y⁻¹) * y := by group
        _ = y⁻¹ * ((y * k * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * k * y⁻¹)) := by rw [hmy]
        _ = y * k * y⁻¹ := by group
    rw [hkm]
    exact hm

private theorem deq2_yElt_eq {H : Subgroup G} (hH : IsHyp Ω H) :
    h.yElt H = (h.exists_unique_yElt hH).choose := by
  unfold yElt
  rw [dif_pos hH]

private theorem deq2_yElt_spec {H : Subgroup G} (hH : IsHyp Ω H) :
    h.yElt H ∈ pCore 2 G ∧ h.yElt H ∉ zGroup Ω ∧
      (∀ g ∈ pSpan (omegaHyp Ω H), g * h.yElt H = h.yElt H * g) ∧
      ∀ y' ∈ pCore 2 G, (∀ g ∈ pSpan (omegaHyp Ω H), g * y' = y' * g) →
        y' = 1 ∨ y' = h.yElt H := by
  rw [deq2_yElt_eq h hH]
  exact (h.exists_unique_yElt hH).choose_spec

theorem yElt_mem_pCore {H : Subgroup G} (hH : IsHyp Ω H) : h.yElt H ∈ pCore 2 G :=
  (h.deq2_yElt_spec hH).1

theorem eq_yElt_of_commute {H : Subgroup G} (hH : IsHyp Ω H) {y : G} (hy : y ∈ pCore 2 G)
    (hy1 : y ≠ 1) (hyc : ∀ g ∈ pSpan (omegaHyp Ω H), g * y = y * g) : y = h.yElt H := by
  rcases (h.deq2_yElt_spec hH).2.2.2 y hy hyc with h1 | h1
  · exact absurd h1 hy1
  · exact h1

theorem yElt_conj {H : Subgroup G} (hH : IsHyp Ω H) (g : G) :
    g * h.yElt H * g⁻¹ = h.yElt (conjSub g H) := by
  have hH' : IsHyp Ω (conjSub g H) := h.isHyp_conjSub hH g
  have hy := h.deq2_yElt_spec hH
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  have hgy : g * h.yElt H * g⁻¹ ∈ pCore 2 G := hQn.conj_mem _ hy.1 g
  have hgy1 : g * h.yElt H * g⁻¹ ≠ 1 := by
    intro e
    apply hy.2.1
    have h1 : h.yElt H = 1 := by
      calc h.yElt H = g⁻¹ * (g * h.yElt H * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    rw [h1]
    exact (zGroup Ω).one_mem
  have hcomm : ∀ g' ∈ pSpan (omegaHyp Ω (conjSub g H)),
      g' * (g * h.yElt H * g⁻¹) = (g * h.yElt H * g⁻¹) * g' := by
    have hle : pSpan (omegaHyp Ω (conjSub g H)) ≤
        Subgroup.centralizer ({g * h.yElt H * g⁻¹} : Set G) := by
      apply pSpan_le
      rintro L ⟨hLΩ, u, hu, hLu⟩ m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hLc : conjSub g⁻¹ L ∈ omegaHyp Ω H := by
        refine ⟨h.hyp.conjInvariant g⁻¹ L hLΩ, g⁻¹ * u * g, ?_, ?_⟩
        · exact mem_conjSub_iff.mp hu
        · have := hLu.conj g⁻¹
          rwa [inv_inv] at this
      have hm' : g⁻¹ * m * g ∈ conjSub g⁻¹ L := by
        rw [mem_conjSub_iff]
        have e : (g⁻¹)⁻¹ * (g⁻¹ * m * g) * g⁻¹ = m := by group
        rw [e]
        exact hm
      have hc := hy.2.2.1 _ (le_pSpan hLc hm')
      calc m * (g * h.yElt H * g⁻¹) = g * ((g⁻¹ * m * g) * h.yElt H) * g⁻¹ := by group
        _ = g * (h.yElt H * (g⁻¹ * m * g)) * g⁻¹ := by rw [hc]
        _ = (g * h.yElt H * g⁻¹) * m := by group
    intro g' hg'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg'))
  exact h.eq_yElt_of_commute hH' hgy hgy1 hcomm

open Classical in
theorem flipVal_yElt {H : Subgroup G} (hH : IsHyp Ω H) {K : Subgroup G} (hK : K ∈ Ω) {x : G}
    (hx : IsUniqueInvolution K x) : flipVal K (h.yElt H) = if x ∈ H then 0 else 1 := by
  have hy := h.deq2_yElt_spec hH
  have hxD : x ∈ zGroup Ω := deq2_involution_mem h hK hx
  have hx1 : x ≠ 1 := hx.ne_one
  obtain ⟨Lf, hLf⟩ := h.deq2_exists_Lf
  split_ifs with hxH
  · exact deq2_flip_zero_of_centralizes h hy.2.2.1 hK hxH hx
  · have hvan : ∀ x' ∈ H, deq2Lam Ω Lf (h.yElt H) x' = 0 := by
      intro x' hx'H
      by_cases hx'1 : x' = 1
      · rw [hx'1]
        simp [deq2Lam]
      · have hx'D : x' ∈ zGroup Ω := (show H ≤ zGroup Ω from hH.1) hx'H
        unfold deq2Lam
        rw [if_pos ⟨hx'D, hx'1⟩]
        exact deq2_flip_zero_of_centralizes h hy.2.2.1 (hLf x' hx'D hx'1).1 hx'H
          (hLf x' hx'D hx'1).2
    have hnz : deq2Lam Ω Lf (h.yElt H) ≠ 0 := fun h0 =>
      hy.2.1 ((h.deq2_lam_eq_zero_iff hLf hy.1).mp h0)
    obtain ⟨H', hH', hF⟩ :=
      h.deq2_dual_eq_fh (h.deq2_lam_mem_dual hLf hy.1) hnz
    have hHH' : H = H' := by
      have hle : H ≤ H' := by
        intro x' hx'H
        have h0 := congrFun hF x'
        rw [hvan x' hx'H] at h0
        have hx'D : x' ∈ zGroup Ω := (show H ≤ zGroup Ω from hH.1) hx'H
        by_contra hn
        simp [deq2Fh, hx'D, hn] at h0
      unfold IsHyp at hH hH'
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hH.2, hH'.2])
    have hKlam : flipVal K (h.yElt H) = deq2Lam Ω Lf (h.yElt H) x := by
      obtain ⟨hLfΩ, hLfx⟩ := hLf x hxD hx1
      have htw := h.flipVal_eq_of_mem_twinSet hLfΩ ⟨hK, x, hLfx, hx⟩ hy.1
      unfold deq2Lam
      rw [if_pos ⟨hxD, hx1⟩, htw]
    rw [hKlam, hF, ← hHH']
    unfold deq2Fh
    simp [hxD, hxH]

omit h in
private theorem deq2_conj_eq_q_mul {Γ : Type*} [Group Γ] {q : Γ} (hq2 : q * q = 1) (g : Γ) :
    g * q * g⁻¹ = q * (q * g * q⁻¹ * g⁻¹) := by
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
  calc g * q * g⁻¹ = (q * q) * (g * q * g⁻¹) := by rw [hq2, one_mul]
    _ = q * (q * g * q * g⁻¹) := by group
    _ = q * (q * g * q⁻¹ * g⁻¹) := by rw [hq']

omit h in
private theorem deq2_four_q {Γ : Type*} [Group Γ] {q a b c : Γ} (hqq : q * q = 1)
    (hqb : q * b = b * q) : q * (q * a) * (q * b) * (q * c) = a * b * c := by
  calc q * (q * a) * (q * b) * (q * c) = (q * q) * a * (q * b) * (q * c) := by group
    _ = a * (q * b) * (q * c) := by rw [hqq, one_mul]
    _ = a * (b * q) * (q * c) := by rw [hqb]
    _ = a * b * (q * q) * c := by group
    _ = a * b * c := by rw [hqq, mul_one]

omit h in
private theorem deq2_comm_pCore {Γ : Type*} [Group Γ] {q g : Γ} (hq : q ∈ pCore 2 Γ) :
    q * g * q⁻¹ * g⁻¹ ∈ pCore 2 Γ := by
  have h1 : g * q⁻¹ * g⁻¹ ∈ pCore 2 Γ :=
    Subgroup.Normal.conj_mem inferInstance q⁻¹ (inv_mem hq) g
  have e : q * g * q⁻¹ * g⁻¹ = q * (g * q⁻¹ * g⁻¹) := by group
  rw [e]
  exact (pCore 2 Γ).mul_mem hq h1

omit h in
private theorem deq2_abab {Γ : Type*} [Group Γ] {A B C : Γ} (hAA : A * A = 1) (hBB : B * B = 1)
    (hBA : B * A = A * B) (hC : C = A * B) : A * B * C = 1 := by
  rw [hC]
  calc A * B * (A * B) = A * (B * A) * B := by group
    _ = A * (A * B) * B := by rw [hBA]
    _ = (A * A) * (B * B) := by group
    _ = 1 := by rw [hAA, hBB, one_mul]

omit h in
private theorem deq2_rearr {Γ : Type*} [Group Γ] {s t x y : Γ} (hxt : x * t = t * x)
    (hys : y * s = s * y) (hxs : x * s = s * x) (hyt : y * t = t * y) :
    s * x * (t * y) * (s * t * y * x) = s * t * s * t * (x * y * y * x) := by
  calc s * x * (t * y) * (s * t * y * x) = s * (x * t) * y * s * t * y * x := by group
    _ = s * (t * x) * y * s * t * y * x := by rw [hxt]
    _ = s * t * x * (y * s) * t * y * x := by group
    _ = s * t * x * (s * y) * t * y * x := by rw [hys]
    _ = s * t * (x * s) * y * t * y * x := by group
    _ = s * t * (s * x) * y * t * y * x := by rw [hxs]
    _ = s * t * s * x * (y * t) * y * x := by group
    _ = s * t * s * x * (t * y) * y * x := by rw [hyt]
    _ = s * t * s * (x * t) * y * y * x := by group
    _ = s * t * s * (t * x) * y * y * x := by rw [hxt]
    _ = s * t * s * t * (x * y * y * x) := by group

omit h in
private theorem deq2_sq_four {Γ : Type*} [Group Γ] {u s t : Γ} (hu : u * u = 1)
    (hss : s * s = u) (htt : t * t = u) (hts : t * s = u * (s * t)) : s * t * s * t = u := by
  have hsu : s * u = u * s := by rw [← hss]; group
  calc s * t * s * t = s * (t * s) * t := by group
    _ = s * (u * (s * t)) * t := by rw [hts]
    _ = (s * u) * s * t * t := by group
    _ = (u * s) * s * t * t := by rw [hsu]
    _ = u * (s * s) * (t * t) := by group
    _ = u * u * u := by rw [hss, htt]
    _ = u := by rw [hu, one_mul]

omit h in
private theorem deq2_caseB_prod {Γ : Type*} [Group Γ] {u s t x y : Γ} (hu : u * u = 1)
    (hss : s * s = u) (htt : t * t = u) (hts : t * s = u * (s * t))
    (hxt : x * t = t * x) (hys : y * s = s * y) (hxs : x * s = s * x) (hyt : y * t = t * y)
    (hxyyx : x * y * y * x = 1) : s * x * (t * y) * (s * t * y * x) = u := by
  rw [deq2_rearr hxt hys hxs hyt, deq2_sq_four hu hss htt hts, hxyyx, mul_one]

theorem norm_identity {K : Subgroup G} (hK : K ∈ Ω) {u i j : G} (hQ : Q8Data K u i j) {q : G}
    (hq : q ∈ pCore 2 G) :
    q * (i * q * i⁻¹) * (j * q * j⁻¹) * ((i * j) * q * (i * j)⁻¹) =
      if flipVal K q = 1 then u else 1 := by
  have hz : IsUniqueInvolution K u := hQ.inv
  have hi : i ∈ K := hQ.mem_i
  have hj : j ∈ K := hQ.mem_j
  have hii : i * i = u := hQ.sq_i
  have hjj : j * j = u := hQ.sq_j
  have hji : j * i = u * (i * j) := hQ.comm
  have hq2 : q * q = 1 := h.pCore_mul_self q hq
  have huQ : u ∈ pCore 2 G := by
    have huI : u ∈ K ⊓ pCore 2 G := by
      rw [h.inf_pCore hK hz]
      exact Subgroup.mem_zpowers u
    exact (Subgroup.mem_inf.mp huI).2
  have hqu : q * u = u * q := h.pCore_comm q hq u huQ
  have hquq : q * u * q⁻¹ = u := by rw [hqu]; group
  have hA : q * i * q⁻¹ * i⁻¹ ∈ pCore 2 G := deq2_comm_pCore hq
  have hB : q * j * q⁻¹ * j⁻¹ ∈ pCore 2 G := deq2_comm_pCore hq
  have hLHS : q * (i * q * i⁻¹) * (j * q * j⁻¹) * ((i * j) * q * (i * j)⁻¹) =
      (q * i * q⁻¹ * i⁻¹) * (q * j * q⁻¹ * j⁻¹) * (q * (i * j) * q⁻¹ * (i * j)⁻¹) := by
    rw [deq2_conj_eq_q_mul hq2 i, deq2_conj_eq_q_mul hq2 j, deq2_conj_eq_q_mul hq2 (i * j)]
    exact deq2_four_q hq2 (h.pCore_comm q hq _ hB)
  rcases deq2_flipVal_cases K q with h0 | h1
  ·
    have hcq : conjSub q K = K := deq2_flipVal_eq_zero_iff.mp h0
    have hqK : ∀ x ∈ K, q * x * q⁻¹ ∈ K := by
      intro x hx
      have hm := conj_mem_conjSub (n := q) hx
      rwa [hcq] at hm
    have hBK : q * j * q⁻¹ * j⁻¹ ∈ K := K.mul_mem (hqK j hj) (K.inv_mem hj)
    have hBz : q * j * q⁻¹ * j⁻¹ ∈ Subgroup.zpowers u := by
      rw [← h.inf_pCore hK hz]
      exact Subgroup.mem_inf.mpr ⟨hBK, hB⟩
    have hiB : i * (q * j * q⁻¹ * j⁻¹) * i⁻¹ = q * j * q⁻¹ * j⁻¹ :=
      conj_of_mem_mem hz hi (deq2_eq_one_or_eq_of_mem_zpowers hz.sq hz.ne_one hBz)
    have hC : q * (i * j) * q⁻¹ * (i * j)⁻¹ = (q * i * q⁻¹ * i⁻¹) * (q * j * q⁻¹ * j⁻¹) := by
      calc q * (i * j) * q⁻¹ * (i * j)⁻¹
          = (q * i * q⁻¹ * i⁻¹) * (i * (q * j * q⁻¹ * j⁻¹) * i⁻¹) := by group
        _ = (q * i * q⁻¹ * i⁻¹) * (q * j * q⁻¹ * j⁻¹) := by rw [hiB]
    have hAA : (q * i * q⁻¹ * i⁻¹) * (q * i * q⁻¹ * i⁻¹) = 1 := h.pCore_mul_self _ hA
    have hBB : (q * j * q⁻¹ * j⁻¹) * (q * j * q⁻¹ * j⁻¹) = 1 := h.pCore_mul_self _ hB
    have hBA : (q * j * q⁻¹ * j⁻¹) * (q * i * q⁻¹ * i⁻¹) =
        (q * i * q⁻¹ * i⁻¹) * (q * j * q⁻¹ * j⁻¹) := h.pCore_comm _ hB _ hA
    rw [if_neg (show ¬ (flipVal K q = 1) by rw [h0]; decide), hLHS]
    exact deq2_abab hAA hBB hBA hC
  ·
    have hne : conjSub q K ≠ K := deq2_flipVal_eq_one_iff.mp h1
    have hJ : conjSub q K ∈ twinSet Ω K := h.conjSub_mem_twinSet hq hK
    have hcomm : Commutes K (conjSub q K) := h.commutes_of_mem_twinSet hK hJ hne
    have hs : q * i * q⁻¹ ∈ conjSub q K := conj_mem_conjSub hi
    have ht : q * j * q⁻¹ ∈ conjSub q K := conj_mem_conjSub hj
    have hxt : i⁻¹ * (q * j * q⁻¹) = (q * j * q⁻¹) * i⁻¹ := hcomm _ (K.inv_mem hi) _ ht
    have hys : j⁻¹ * (q * i * q⁻¹) = (q * i * q⁻¹) * j⁻¹ := hcomm _ (K.inv_mem hj) _ hs
    have hxs : i⁻¹ * (q * i * q⁻¹) = (q * i * q⁻¹) * i⁻¹ := hcomm _ (K.inv_mem hi) _ hs
    have hyt : j⁻¹ * (q * j * q⁻¹) = (q * j * q⁻¹) * j⁻¹ := hcomm _ (K.inv_mem hj) _ ht
    have hss : (q * i * q⁻¹) * (q * i * q⁻¹) = u := by
      calc (q * i * q⁻¹) * (q * i * q⁻¹) = q * (i * i) * q⁻¹ := by group
        _ = q * u * q⁻¹ := by rw [hii]
        _ = u := hquq
    have htt : (q * j * q⁻¹) * (q * j * q⁻¹) = u := by
      calc (q * j * q⁻¹) * (q * j * q⁻¹) = q * (j * j) * q⁻¹ := by group
        _ = q * u * q⁻¹ := by rw [hjj]
        _ = u := hquq
    have hts : (q * j * q⁻¹) * (q * i * q⁻¹) = u * ((q * i * q⁻¹) * (q * j * q⁻¹)) := by
      calc (q * j * q⁻¹) * (q * i * q⁻¹) = q * (j * i) * q⁻¹ := by group
        _ = q * (u * (i * j)) * q⁻¹ := by rw [hji]
        _ = (q * u * q⁻¹) * ((q * i * q⁻¹) * (q * j * q⁻¹)) := by group
        _ = u * ((q * i * q⁻¹) * (q * j * q⁻¹)) := by rw [hquq]
    have hiu : i⁻¹ * u = u * i⁻¹ := by rw [← hii]; group
    have hyy : j⁻¹ * j⁻¹ = u := by
      rw [← mul_inv_rev, hjj, inv_eq_of_mul_eq_one_right hz.sq]
    have hxyyx : i⁻¹ * j⁻¹ * j⁻¹ * i⁻¹ = 1 := by
      calc i⁻¹ * j⁻¹ * j⁻¹ * i⁻¹ = i⁻¹ * (j⁻¹ * j⁻¹) * i⁻¹ := by group
        _ = i⁻¹ * u * i⁻¹ := by rw [hyy]
        _ = u * i⁻¹ * i⁻¹ := by rw [hiu]
        _ = u * (i * i)⁻¹ := by group
        _ = u * u⁻¹ := by rw [hii]
        _ = 1 := mul_inv_cancel u
    have hC : q * (i * j) * q⁻¹ * (i * j)⁻¹ = (q * i * q⁻¹) * (q * j * q⁻¹) * j⁻¹ * i⁻¹ := by
      group
    rw [if_pos h1, hLHS, hC]
    exact deq2_caseB_prod hz.sq hss htt hts hxt hys hxs hyt hxyyx

@[expose] def deq2Dot (f v : Fin 3 → ZMod 2) : ZMod 2 := f 0 * v 0 + f 1 * v 1 + f 2 * v 2

@[expose] def deq2T (f : Fin 3 → ZMod 2) : Fin 7 :=
  if f = ![1, 0, 0] then 2 else if f = ![0, 1, 0] then 1 else if f = ![0, 0, 1] then 0
  else if f = ![1, 1, 0] then 4 else if f = ![1, 0, 1] then 6 else if f = ![0, 1, 1] then 3
  else if f = ![1, 1, 1] then 5 else 0

omit h in
private theorem deq2_T_inj : ∀ f f' : Fin 3 → ZMod 2, f ≠ 0 → f' ≠ 0 →
    deq2T f = deq2T f' → f = f' := by
  decide

omit h in
private theorem deq2_T_surj : ∀ i : Fin 7, ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ deq2T f = i := by
  decide

omit h in
private theorem deq2_dot_ker_inj : ∀ f f' : Fin 3 → ZMod 2, f ≠ 0 → f' ≠ 0 →
    (∀ v : Fin 3 → ZMod 2, deq2Dot f v = 0 ↔ deq2Dot f' v = 0) → f = f' := by
  decide

omit h in
private theorem deq2_card_ker : ∀ f : Fin 3 → ZMod 2, f ≠ 0 →
    (Finset.univ.filter (fun v : Fin 3 → ZMod 2 => deq2Dot f v = 0)).card = 4 := by
  decide

omit h in
private theorem deq2_line_of_vec : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ ℓ ∈ AE.fanoLines, ∀ f : Fin 3 → ZMod 2, f ≠ 0 → (deq2Dot f v = 0 ↔ deq2T f ∈ ℓ) := by
  decide

omit h in
private theorem deq2_vec_of_line : ∀ s ∈ AE.fanoLines, ∃ v : Fin 3 → ZMod 2, v ≠ 0 ∧
    ∀ f : Fin 3 → ZMod 2, f ≠ 0 → (deq2T f ∈ s ↔ deq2Dot f v = 0) := by
  decide

@[expose] def deq2K (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e) (f : Fin 3 → ZMod 2) :
    Subgroup G where
  carrier := {x | ∃ v, TL4.e8Coord e v = x ∧ deq2Dot f v = 0}
  mul_mem' := by
    rintro _ _ ⟨u, rfl, hu⟩ ⟨v, rfl, hv⟩
    refine ⟨u + v, TL4.e8Coord_add he u v, ?_⟩
    simp only [deq2Dot, Pi.add_apply] at hu hv ⊢
    linear_combination hu + hv
  one_mem' := ⟨0, TL4.e8Coord_zero, by simp [deq2Dot]⟩
  inv_mem' := by
    rintro _ ⟨v, rfl, hv⟩
    exact ⟨v, (inv_eq_of_mul_eq_one_right (he.sq _ (TL4.e8Coord_mem he v))).symm, hv⟩

omit h in
private theorem deq2_mem_deq2K (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e)
    (f v : Fin 3 → ZMod 2) : TL4.e8Coord e v ∈ deq2K e he f ↔ deq2Dot f v = 0 := by
  constructor
  · rintro ⟨w, hw, hf⟩
    rwa [TL4.e8Coord_injective he hw] at hf
  · intro hv
    exact ⟨v, rfl, hv⟩

omit h in
private theorem deq2_eq_of_deq2K_eq (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e)
    {f f' : Fin 3 → ZMod 2} (hf : f ≠ 0) (hf' : f' ≠ 0) (hK : deq2K e he f = deq2K e he f') :
    f = f' := by
  refine deq2_dot_ker_inj f f' hf hf' fun v => ?_
  rw [← deq2_mem_deq2K e he f v, ← deq2_mem_deq2K e he f' v, hK]

omit h in
private theorem deq2_card_deq2K (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e)
    {f : Fin 3 → ZMod 2} (hf : f ≠ 0) : Nat.card (deq2K e he f) = 4 := by
  have hk : Nat.card {v : Fin 3 → ZMod 2 // deq2Dot f v = 0} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, deq2_card_ker f hf]
  rw [← hk]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun v : {v : Fin 3 → ZMod 2 // deq2Dot f v = 0} =>
      (⟨TL4.e8Coord e v.1, v.1, rfl, v.2⟩ : deq2K e he f)) ⟨?_, ?_⟩)).symm
  · rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
    exact Subtype.ext (TL4.e8Coord_injective he (congrArg Subtype.val hvw))
  · rintro ⟨x, v, rfl, hv⟩
    exact ⟨⟨v, hv⟩, rfl⟩

omit h in
private theorem deq2_isHyp (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e)
    {f : Fin 3 → ZMod 2} (hf : f ≠ 0) : IsHyp Ω (deq2K e he f) := by
  refine ⟨fun x hx => ?_, deq2_card_deq2K e he hf⟩
  obtain ⟨v, rfl, -⟩ := hx
  exact TL4.e8Coord_mem he v

theorem deq2_exists_eq_deq2K (e : Fin 3 → G) (he : TL4.E8Basis (zGroup Ω) e)
    {H : Subgroup G} (hH : IsHyp Ω H) : ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ deq2K e he f = H := by
  have hS : Set.ncard {H : Subgroup G | IsHyp Ω H} = 7 := h.card_isHyp
  have hN : Set.ncard {f : Fin 3 → ZMod 2 | f ≠ 0} = 7 := by
    have hset : {f : Fin 3 → ZMod 2 | f ≠ 0} = ↑(Finset.univ.erase (0 : Fin 3 → ZMod 2)) := by
      ext f
      simp
    rw [hset, Set.ncard_coe_finset]
    decide
  have hinj : Set.InjOn (deq2K e he) {f : Fin 3 → ZMod 2 | f ≠ 0} :=
    fun f hf f' hf' hK => deq2_eq_of_deq2K_eq e he hf hf' hK
  have himg : (deq2K e he '' {f : Fin 3 → ZMod 2 | f ≠ 0}).ncard = 7 := by
    rw [hinj.ncard_image, hN]
  have hsub : deq2K e he '' {f : Fin 3 → ZMod 2 | f ≠ 0} ⊆ {H : Subgroup G | IsHyp Ω H} := by
    rintro _ ⟨f, hf, rfl⟩
    exact deq2_isHyp e he hf
  have hfin : {H : Subgroup G | IsHyp Ω H}.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hS]; norm_num)
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [himg, hS])) hfin
  have hmem : H ∈ deq2K e he '' {f : Fin 3 → ZMod 2 | f ≠ 0} := by
    rw [heq]
    exact hH
  obtain ⟨f, hf, hfH⟩ := hmem
  exact ⟨f, hf, hfH⟩

theorem deq2_labelling : ∃ (lab : Subgroup G → Fin 7) (σ : G →* Equiv.Perm (Fin 7)),
    (∀ H H' : Subgroup G, IsHyp Ω H → IsHyp Ω H' → lab H = lab H' → H = H') ∧
    (∀ i : Fin 7, ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i) ∧
    (∀ (g : G) (H : Subgroup G), IsHyp Ω H → lab (conjSub g H) = σ g (lab H)) ∧
    (∀ g : G, σ g ∈ AE.l32) ∧
    (∀ x ∈ zGroup Ω, x ≠ 1 →
      ∃ ℓ ∈ AE.fanoLines, ∀ H : Subgroup G, IsHyp Ω H → (x ∈ H ↔ lab H ∈ ℓ)) := by
  obtain ⟨e, he⟩ := h.exists_basis
  have hcov : ∀ H : Subgroup G, IsHyp Ω H → ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ deq2K e he f = H :=
    fun H hH => h.deq2_exists_eq_deq2K e he hH
  choose! F hF using hcov
  obtain ⟨lab, hlab⟩ : ∃ lab : Subgroup G → Fin 7, ∀ H, lab H = deq2T (F H) :=
    ⟨_, fun H => rfl⟩
  have hFK : ∀ f : Fin 3 → ZMod 2, f ≠ 0 → F (deq2K e he f) = f := fun f hf =>
    deq2_eq_of_deq2K_eq e he (hF _ (deq2_isHyp e he hf)).1 hf (hF _ (deq2_isHyp e he hf)).2
  have hlab_deq : ∀ f : Fin 3 → ZMod 2, f ≠ 0 → lab (deq2K e he f) = deq2T f := by
    intro f hf
    rw [hlab, hFK f hf]
  choose Fi hFi using deq2_T_surj
  obtain ⟨Hof, hHof⟩ : ∃ Hof : Fin 7 → Subgroup G, ∀ i, Hof i = deq2K e he (Fi i) :=
    ⟨_, fun i => rfl⟩
  have hHof_hyp : ∀ i, IsHyp Ω (Hof i) := fun i => by
    rw [hHof]
    exact deq2_isHyp e he (hFi i).1
  have hlab_Hof : ∀ i, lab (Hof i) = i := fun i => by
    rw [hHof, hlab_deq _ (hFi i).1, (hFi i).2]
  have hHof_lab : ∀ H : Subgroup G, IsHyp Ω H → Hof (lab H) = H := by
    intro H hH
    have hFi' : Fi (deq2T (F H)) = F H :=
      deq2_T_inj _ _ (hFi (deq2T (F H))).1 (hF H hH).1 (hFi (deq2T (F H))).2
    rw [hHof, hlab, hFi', (hF H hH).2]
  have hlab_inj : ∀ H H' : Subgroup G, IsHyp Ω H → IsHyp Ω H' → lab H = lab H' → H = H' := by
    intro H H' hH hH' hl
    rw [hlab, hlab] at hl
    have hFe := deq2_T_inj _ _ (hF H hH).1 (hF H' hH').1 hl
    exact (hF H hH).2.symm.trans ((congrArg (deq2K e he) hFe).trans (hF H' hH').2)
  have hlab_surj : ∀ i : Fin 7, ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i :=
    fun i => ⟨Hof i, hHof_hyp i, hlab_Hof i⟩
  obtain ⟨act, hact⟩ : ∃ act : G → Fin 7 → Fin 7, ∀ g i, act g i = lab (conjSub g (Hof i)) :=
    ⟨_, fun _ _ => rfl⟩
  have hact_one : ∀ i, act 1 i = i := fun i => by
    rw [hact, conjSub_one, hlab_Hof]
  have hact_mul : ∀ g k i, act (g * k) i = act g (act k i) := by
    intro g k i
    simp only [hact]
    rw [hHof_lab _ (h.isHyp_conjSub (hHof_hyp i) k), conjSub_mul]
  have hact_inv_left : ∀ g i, act g⁻¹ (act g i) = i := fun g i => by
    rw [← hact_mul, inv_mul_cancel, hact_one]
  have hact_inv_right : ∀ g i, act g (act g⁻¹ i) = i := fun g i => by
    rw [← hact_mul, mul_inv_cancel, hact_one]
  obtain ⟨σ, hσ⟩ : ∃ σ : G →* Equiv.Perm (Fin 7), ∀ g i, σ g i = act g i :=
    ⟨{ toFun := fun g => ⟨act g, act g⁻¹, hact_inv_left g, hact_inv_right g⟩
       map_one' := Equiv.ext hact_one
       map_mul' := fun g k => Equiv.ext (hact_mul g k) }, fun _ _ => rfl⟩
  have hlab_conj : ∀ (g : G) (H : Subgroup G), IsHyp Ω H → lab (conjSub g H) = σ g (lab H) := by
    intro g H hH
    rw [hσ, hact, hHof_lab H hH]
  have hline_w : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
      ∃ ℓ ∈ AE.fanoLines, ∀ H : Subgroup G, IsHyp Ω H → (TL4.e8Coord e w ∈ H ↔ lab H ∈ ℓ) := by
    intro w hw
    obtain ⟨ℓ, hℓ, hfl⟩ := deq2_line_of_vec w hw
    refine ⟨ℓ, hℓ, fun H hH => ?_⟩
    have key := deq2_mem_deq2K e he (F H) w
    rw [(hF H hH).2] at key
    rw [hlab]
    exact key.trans (hfl (F H) (hF H hH).1)
  have hline : ∀ x ∈ zGroup Ω, x ≠ 1 →
      ∃ ℓ ∈ AE.fanoLines, ∀ H : Subgroup G, IsHyp Ω H → (x ∈ H ↔ lab H ∈ ℓ) := by
    intro x hx hx1
    obtain ⟨w, rfl⟩ := TL4.exists_e8Coord_eq he hx
    have hw : w ≠ 0 := fun hw => hx1 (by rw [hw, TL4.e8Coord_zero])
    exact hline_w w hw
  have hmemline : ∀ (s : Finset (Fin 7)) (v : Fin 3 → ZMod 2),
      (∀ f : Fin 3 → ZMod 2, f ≠ 0 → (deq2T f ∈ s ↔ deq2Dot f v = 0)) →
      ∀ j : Fin 7, j ∈ s ↔ TL4.e8Coord e v ∈ Hof j := by
    intro s v hsv j
    have hj : j ∈ s ↔ deq2T (Fi j) ∈ s := by rw [(hFi j).2]
    rw [hj, hsv (Fi j) (hFi j).1, hHof, deq2_mem_deq2K e he]
  have hfwd : ∀ (g : G) (s : Finset (Fin 7)), s ∈ AE.fanoLines →
      s.map (σ g).toEmbedding ∈ AE.fanoLines := by
    intro g s hs
    obtain ⟨v, hv0, hsv⟩ := deq2_vec_of_line s hs
    have hmem := hmemline s v hsv
    have hx1 : TL4.e8Coord e v ≠ 1 := fun h2 => hv0 (TL4.eq_zero_of_e8Coord_eq_one he h2)
    obtain ⟨y, hy⟩ : ∃ y, y = g * TL4.e8Coord e v * g⁻¹ := ⟨_, rfl⟩
    have hyD : y ∈ zGroup Ω := by
      rw [hy]
      exact h.zGroup_normal.conj_mem _ (TL4.e8Coord_mem he v) g
    have hy1 : y ≠ 1 := by
      intro h1
      apply hx1
      rw [hy] at h1
      calc TL4.e8Coord e v = g⁻¹ * (g * TL4.e8Coord e v * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨w, hw⟩ := TL4.exists_e8Coord_eq he hyD
    have hw0 : w ≠ 0 := fun h0 => hy1 (by rw [← hw, h0, TL4.e8Coord_zero])
    obtain ⟨ℓ, hℓ, hfl⟩ := hline_w w hw0
    have key : ∀ i : Fin 7, i ∈ s.map (σ g).toEmbedding ↔ i ∈ ℓ := by
      intro i
      rw [Finset.mem_map_equiv]
      obtain ⟨j, hj⟩ : ∃ j, (σ g).symm i = j := ⟨_, rfl⟩
      have hσj : σ g j = i := by
        rw [← hj]
        exact (σ g).apply_symm_apply i
      rw [hj, hmem j]
      have hHi : Hof i = conjSub g (Hof j) := by
        rw [← hσj, hσ, hact, hHof_lab _ (h.isHyp_conjSub (hHof_hyp j) g)]
      have hconj : y ∈ conjSub g (Hof j) ↔ TL4.e8Coord e v ∈ Hof j := by
        have hgy : g⁻¹ * y * g = TL4.e8Coord e v := by
          rw [hy]
          group
        rw [mem_conjSub_iff, hgy]
      have hline_i : TL4.e8Coord e w ∈ Hof i ↔ i ∈ ℓ := by
        have := hfl (Hof i) (hHof_hyp i)
        rwa [hlab_Hof i] at this
      rw [← hline_i, hw, hHi]
      exact hconj.symm
    have heq : s.map (σ g).toEmbedding = ℓ := Finset.ext key
    rw [heq]
    exact hℓ
  have hσmem : ∀ g : G, σ g ∈ AE.l32 := by
    intro g
    unfold AE.l32 AE.stabFamily
    refine fun s hs => ⟨hfwd g s hs, ?_⟩
    have h2 := hfwd g⁻¹ s hs
    rwa [map_inv] at h2
  exact ⟨lab, σ, hlab_inj, hlab_surj, hlab_conj, hσmem, hline⟩

section DeqCoord

variable {A : Type} [CommGroup A]

omit h in
private theorem deq2_pow_val_add {y : A} (hy : y * y = 1) (a b : ZMod 2) :
    y ^ (a + b).val = y ^ a.val * y ^ b.val := by
  have hy2 : y ^ 2 = 1 := by rw [sq]; exact hy
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val + b.val) hy2).symm

private def deq2_coord (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1) :
    Multiplicative (Fin 7 → ZMod 2) →* A where
  toFun f := ∏ i, y i ^ (f.toAdd i).val
  map_one' := by simp
  map_mul' f g := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => deq2_pow_val_add (hy i) _ _

omit h in
private theorem deq2_coord_apply (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1)
    (f : Multiplicative (Fin 7 → ZMod 2)) :
    deq2_coord y hy f = ∏ i, y i ^ (f.toAdd i).val := rfl

omit h in
private theorem deq2_coord_single (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1) (i : Fin 7) :
    deq2_coord y hy (Multiplicative.ofAdd (Pi.single i 1)) = y i := by
  rw [deq2_coord_apply, Finset.prod_eq_single i]
  · simp only [toAdd_ofAdd]
    rw [Pi.single_eq_same, show (1 : ZMod 2).val = 1 from rfl, pow_one]
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit h in
private theorem deq2_coord_map (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1) (φ : A →* A)
    (σ : Equiv.Perm (Fin 7)) (hφ : ∀ i, φ (y i) = y (σ i))
    (f : Multiplicative (Fin 7 → ZMod 2)) :
    φ (deq2_coord y hy f) =
      deq2_coord y hy (Multiplicative.ofAdd fun j => f.toAdd (σ.symm j)) := by
  rw [deq2_coord_apply, deq2_coord_apply, map_prod]
  simp only [map_pow, hφ, toAdd_ofAdd]
  refine Eq.trans ?_ (Equiv.prod_comp σ (fun j => y j ^ (f.toAdd (σ.symm j)).val))
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

omit h in
private theorem deq2_coord_card_ker (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1)
    (hsurj : Function.Surjective (deq2_coord y hy)) (hA : Nat.card A = 64) :
    Nat.card (deq2_coord y hy).ker = 2 := by
  have h1 := Subgroup.card_mul_index (deq2_coord y hy).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hA] at h1
  have hM : Nat.card (Multiplicative (Fin 7 → ZMod 2)) = 128 := by
    simp [Nat.card_eq_fintype_card]
  omega

omit h in
private theorem deq2_coord_ker_eq (y : Fin 7 → A) (hy : ∀ i, y i * y i = 1)
    (hcard : Nat.card (deq2_coord y hy).ker = 2) :
    ∃ r : Multiplicative (Fin 7 → ZMod 2), deq2_coord y hy r = 1 ∧ r ≠ 1 ∧
      ∀ f, deq2_coord y hy f = 1 → f = 1 ∨ f = r := by
  obtain ⟨r, hr1, hru⟩ := (Nat.card_eq_two_iff' (1 : (deq2_coord y hy).ker)).mp hcard
  refine ⟨r.1, MonoidHom.mem_ker.mp r.2, fun e => hr1 (Subtype.ext e), fun f hf => ?_⟩
  by_cases hf1 : f = 1
  · exact Or.inl hf1
  · right
    have := hru ⟨f, (MonoidHom.mem_ker).mpr hf⟩ (fun e => hf1 (congrArg Subtype.val e))
    exact congrArg Subtype.val this

end DeqCoord

private def deq2_conjQ {X : Type} [Group X] (S : Subgroup X) (g : X)
    (hS : ∀ x ∈ S, g * x * g⁻¹ ∈ S) : S →* S where
  toFun x := ⟨g * x * g⁻¹, hS x x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private abbrev deq2_commGroup {X : Type} [Group X] (S : Subgroup X)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : CommGroup S :=
  { (inferInstance : Group S) with
    mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }

private theorem deq2_conj_eq_zGroup {H : Subgroup G} (hH : H ≤ zGroup Ω) {z : G}
    (hz : z ∈ zGroup Ω) : conjSub z H = H := by
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have e : z * (z⁻¹ * y * z) = (z⁻¹ * y * z) * z := h.zGroup_comm z hz _ (hH hy)
    have hy' : y = z⁻¹ * y * z := by
      calc y = (z * (z⁻¹ * y * z)) * z⁻¹ := by group
        _ = ((z⁻¹ * y * z) * z) * z⁻¹ := by rw [e]
        _ = z⁻¹ * y * z := by group
    rw [hy']
    exact hy
  · intro hy
    have e : z⁻¹ * y * z = y := by
      have hc := h.zGroup_comm z hz y (hH hy)
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    rw [e]
    exact hy

open Classical in
theorem deq2_beta (lab : Subgroup G → Fin 7) (σ : G →* Equiv.Perm (Fin 7))
    (hinj : ∀ H H' : Subgroup G, IsHyp Ω H → IsHyp Ω H' → lab H = lab H' → H = H')
    (hsurj : ∀ i : Fin 7, ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i)
    (hconj : ∀ (g : G) (H : Subgroup G), IsHyp Ω H → lab (conjSub g H) = σ g (lab H)) :
    ∃ β : Multiplicative (Fin 7 → ZMod 2) →* G,
      β.range = pCore 2 G ∧
      (∀ f : Multiplicative (Fin 7 → ZMod 2), β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1) ∧
      (∀ (g : G) (f : Multiplicative (Fin 7 → ZMod 2)),
        g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ g).symm i))) ∧
      (∀ x ∈ zGroup Ω, x ≠ 1 → x = β (Multiplicative.ofAdd fun i =>
        if ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H then 1 else 0)) := by
  classical
  choose Hs hHs hlabs using hsurj
  have hsH : ∀ H, IsHyp Ω H → Hs (lab H) = H := fun H hH => hinj _ _ (hHs _) hH (hlabs _)
  have hQn : (pCore 2 G).Normal := by
    rw [← h.centralizer_zGroup_eq_pCore]
    exact h.centralizer_zGroup_normal
  letI : CommGroup (pCore 2 G) :=
    deq2_commGroup (pCore 2 G) (fun a ha b hb => h.pCore_comm a ha b hb)
  obtain ⟨y, hy_def⟩ : ∃ y : Fin 7 → pCore 2 G, ∀ i, ((y i : pCore 2 G) : G) = h.yElt (Hs i) :=
    ⟨fun i => ⟨h.yElt (Hs i), h.yElt_mem_pCore (hHs i)⟩, fun i => rfl⟩
  have hy : ∀ i, y i * y i = 1 := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_mul, hy_def, Subgroup.coe_one]
    exact h.pCore_mul_self _ (h.yElt_mem_pCore (hHs i))
  obtain ⟨cQ, hcQ⟩ : ∃ cQ : G → pCore 2 G →* pCore 2 G,
      ∀ (g : G) (x : pCore 2 G), ((cQ g x : pCore 2 G) : G) = g * x * g⁻¹ :=
    ⟨fun g => deq2_conjQ (pCore 2 G) g (fun x hx => hQn.conj_mem x hx g), fun g x => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Multiplicative (Fin 7 → ZMod 2) →* G,
      ∀ f, β f = ((deq2_coord y hy f : pCore 2 G) : G) :=
    ⟨(pCore 2 G).subtype.comp (deq2_coord y hy), fun f => rfl⟩
  have hconjHs : ∀ (g : G) (i : Fin 7), conjSub g (Hs i) = Hs (σ g i) := by
    intro g i
    have e := hsH _ (h.isHyp_conjSub (hHs i) g)
    rw [hconj g (Hs i) (hHs i), hlabs i] at e
    exact e.symm
  have hφ : ∀ (g : G) (i : Fin 7), cQ g (y i) = y (σ g i) := by
    intro g i
    apply Subtype.ext
    rw [hcQ, hy_def, hy_def, h.yElt_conj (hHs i) g, hconjHs g i]
  have hconj_eq : ∀ (g : G) (f : Multiplicative (Fin 7 → ZMod 2)),
      g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ g).symm i)) := by
    intro g f
    rw [hβ, hβ, ← hcQ]
    exact congrArg Subtype.val (deq2_coord_map y hy (cQ g) (σ g) (hφ g) f)
  have hsingle : ∀ H, IsHyp Ω H →
      β (Multiplicative.ofAdd (Pi.single (lab H) 1)) = h.yElt H := by
    intro H hH
    rw [hβ, deq2_coord_single, hy_def, hsH H hH]
  obtain ⟨Lf, hLf⟩ := h.deq2_exists_Lf
  have hLamY : ∀ H, IsHyp Ω H → deq2Lam Ω Lf (h.yElt H) = deq2Fh Ω H := by
    intro H hH
    funext x
    unfold deq2Lam deq2Fh
    by_cases hx : x ∈ zGroup Ω ∧ x ≠ 1
    · obtain ⟨hK, hxK⟩ := hLf x hx.1 hx.2
      rw [if_pos hx, h.flipVal_yElt hH hK hxK]
      by_cases hxH : x ∈ H
      · simp [hxH]
      · simp [hxH, hx.1]
    · rw [if_neg hx]
      by_cases hxD : x ∈ zGroup Ω
      · have hx1 : x = 1 := by
          by_contra hne
          exact hx ⟨hxD, hne⟩
        subst hx1
        simp
      · simp [hxD]
  have hzRel : ∀ x ∈ zGroup Ω, x ≠ 1 → x = β (Multiplicative.ofAdd fun i =>
      if ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H then 1 else 0) := by
    intro x hxD hx1
    obtain ⟨hK, hxK⟩ := hLf x hxD hx1
    have hxx : x * x = 1 := h.zGroup_mul_self x hxD
    obtain ⟨H₀, hH₀, hx₀⟩ : ∃ H₀ : Subgroup G, IsHyp Ω H₀ ∧ x ∉ H₀ := by
      obtain ⟨q₀, hq₀, hf₀⟩ := h.exists_flip hK
      have hne : deq2Lam Ω Lf q₀ ≠ 0 := by
        intro h0
        have h1 : deq2Lam Ω Lf q₀ x = 0 := congrFun h0 x
        unfold deq2Lam at h1
        rw [if_pos (show x ∈ zGroup Ω ∧ x ≠ 1 from ⟨hxD, hx1⟩), hf₀] at h1
        exact absurd h1 (by decide)
      obtain ⟨H₀, hH₀, hF⟩ := h.deq2_dual_eq_fh (h.deq2_lam_mem_dual hLf hq₀) hne
      refine ⟨H₀, hH₀, fun hxH => ?_⟩
      have h1 : deq2Lam Ω Lf q₀ x = deq2Fh Ω H₀ x := congrFun hF x
      unfold deq2Lam deq2Fh at h1
      rw [if_pos (show x ∈ zGroup Ω ∧ x ≠ 1 from ⟨hxD, hx1⟩), hf₀,
        if_neg (fun hh : x ∈ zGroup Ω ∧ x ∉ H₀ => hh.2 hxH)] at h1
      exact absurd h1 (by decide)
    obtain ⟨a, b, hQ⟩ := deq2_exists_q8 hxK (h.isQuatSub_of_mem hK) (h.card _ hK)
    have hxa : x * a = a * x := by
      rw [← hQ.sq_i]
      exact mul_assoc a a a
    have hxb : x * b = b * x := by
      rw [← hQ.sq_j]
      exact mul_assoc b b b
    have hxab : x * (a * b) = a * b * x := by
      rw [← mul_assoc, hxa, mul_assoc a x b, hxb, ← mul_assoc]
    have hab_sq : a * b * (a * b) = x := by
      calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (x * (a * b)) * b := by rw [hQ.comm]
        _ = (a * x) * (a * b) * b := by simp only [mul_assoc]
        _ = (x * a) * (a * b) * b := by rw [← hxa]
        _ = x * (a * a) * (b * b) := by simp only [mul_assoc]
        _ = x * x * x := by rw [hQ.sq_i, hQ.sq_j]
        _ = x := by rw [hxx, one_mul]
    have ha1 : a ≠ 1 := by
      intro e
      apply hx1
      rw [← hQ.sq_i, e, one_mul]
    have hb1 : b ≠ 1 := by
      intro e
      apply hx1
      rw [← hQ.sq_j, e, one_mul]
    have hax : a ≠ x := by
      intro e
      apply hx1
      have h2 := hQ.sq_i
      rw [e, hxx] at h2
      exact h2.symm
    have hbx : b ≠ x := by
      intro e
      apply hx1
      have h2 := hQ.sq_j
      rw [e, hxx] at h2
      exact h2.symm
    have hab1 : a * b ≠ 1 := by
      intro e
      have h2 : b * a = 1 := by
        rw [eq_inv_of_mul_eq_one_right e, inv_mul_cancel]
      have h3 := hQ.comm
      rw [h2, e, mul_one] at h3
      exact hx1 h3.symm
    have habx : a * b ≠ x := by
      intro e
      have h2 := hab_sq
      rw [e, hxx] at h2
      exact hx1 h2.symm
    have hab' : a ≠ b := by
      intro e
      apply hx1
      have h2 := hQ.comm
      rw [← e, hQ.sq_i, hxx] at h2
      exact h2
    have hbax : b ≠ a * x := by
      intro e
      have h2 : b * a = 1 := by
        rw [e, mul_assoc, hxa, ← mul_assoc, hQ.sq_i, hxx]
      have h3 : a * b = x := by
        have h4 := hQ.comm
        rw [h2] at h4
        calc a * b = x * (x * (a * b)) := by rw [← mul_assoc, hxx, one_mul]
          _ = x := by rw [← h4, mul_one]
      exact habx h3
    have hH₁ : IsHyp Ω (conjSub a H₀) := h.isHyp_conjSub hH₀ a
    have hH₂ : IsHyp Ω (conjSub b H₀) := h.isHyp_conjSub hH₀ b
    have hH₃ : IsHyp Ω (conjSub (a * b) H₀) := h.isHyp_conjSub hH₀ (a * b)
    have hxconj : ∀ g : G, g⁻¹ * x * g = x → x ∉ conjSub g H₀ := by
      intro g hg hm
      rw [mem_conjSub_iff, hg] at hm
      exact hx₀ hm
    have hxa' : a⁻¹ * x * a = x := by
      rw [mul_assoc, hxa, ← mul_assoc, inv_mul_cancel, one_mul]
    have hxb' : b⁻¹ * x * b = x := by
      rw [mul_assoc, hxb, ← mul_assoc, inv_mul_cancel, one_mul]
    have hxab' : (a * b)⁻¹ * x * (a * b) = x := by
      rw [mul_assoc, hxab, ← mul_assoc, inv_mul_cancel, one_mul]
    have hx₁ : x ∉ conjSub a H₀ := hxconj a hxa'
    have hx₂ : x ∉ conjSub b H₀ := hxconj b hxb'
    have hx₃ : x ∉ conjSub (a * b) H₀ := hxconj (a * b) hxab'
    have hconj_inj : ∀ k l : G, k ∈ Lf x → l ∈ Lf x → conjSub k H₀ = conjSub l H₀ →
        k⁻¹ * l = 1 ∨ k⁻¹ * l = x := by
      intro k l hk hl hkl
      apply deq2_eq_one_or_eq_of_mem_zpowers hxx hx1
      rw [← h.inf_normalizer_hyp_of_not_mem hK hxK hH₀ hx₀]
      refine Subgroup.mem_inf.mpr ⟨(Lf x).mul_mem ((Lf x).inv_mem hk) hl, ?_⟩
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← hkl, conjSub_inv_conjSub]
    have hdist : ∀ k l : G, k ∈ Lf x → l ∈ Lf x → k⁻¹ * l ≠ 1 → k⁻¹ * l ≠ x →
        conjSub k H₀ ≠ conjSub l H₀ := by
      intro k l hk hl h1 h2 e
      rcases hconj_inj k l hk hl e with h3 | h3
      · exact h1 h3
      · exact h2 h3
    have hA1 : (1 : G) ∈ Lf x := (Lf x).one_mem
    have hAa : a ∈ Lf x := hQ.mem_i
    have hAb : b ∈ Lf x := hQ.mem_j
    have hAab : a * b ∈ Lf x := (Lf x).mul_mem hQ.mem_i hQ.mem_j
    have hd01 : H₀ ≠ conjSub a H₀ := by
      have := hdist 1 a hA1 hAa (by simpa using ha1) (by simpa using hax)
      rwa [conjSub_one] at this
    have hd02 : H₀ ≠ conjSub b H₀ := by
      have := hdist 1 b hA1 hAb (by simpa using hb1) (by simpa using hbx)
      rwa [conjSub_one] at this
    have hd03 : H₀ ≠ conjSub (a * b) H₀ := by
      have := hdist 1 (a * b) hA1 hAab (by simpa using hab1) (by simpa using habx)
      rwa [conjSub_one] at this
    have hd12 : conjSub a H₀ ≠ conjSub b H₀ :=
      hdist a b hAa hAb (fun e => hab' (inv_mul_eq_one.mp e))
        (fun e => hbax (by rw [← e, mul_inv_cancel_left]))
    have hd13 : conjSub a H₀ ≠ conjSub (a * b) H₀ :=
      hdist a (a * b) hAa hAab (by rw [inv_mul_cancel_left]; exact hb1)
        (by rw [inv_mul_cancel_left]; exact hbx)
    have hd23 : conjSub b H₀ ≠ conjSub (a * b) H₀ :=
      hdist b (a * b) hAb hAab
        (fun e => ha1 (mul_right_cancel (b := b)
          (by rw [one_mul]; exact (inv_mul_eq_one.mp e).symm)))
        (fun e => hax (mul_right_cancel (b := b)
          (by rw [hxb, ← e, mul_inv_cancel_left])))
    have hl01 : lab H₀ ≠ lab (conjSub a H₀) := fun e => hd01 (hinj _ _ hH₀ hH₁ e)
    have hl02 : lab H₀ ≠ lab (conjSub b H₀) := fun e => hd02 (hinj _ _ hH₀ hH₂ e)
    have hl03 : lab H₀ ≠ lab (conjSub (a * b) H₀) := fun e => hd03 (hinj _ _ hH₀ hH₃ e)
    have hl12 : lab (conjSub a H₀) ≠ lab (conjSub b H₀) := fun e => hd12 (hinj _ _ hH₁ hH₂ e)
    have hl13 : lab (conjSub a H₀) ≠ lab (conjSub (a * b) H₀) :=
      fun e => hd13 (hinj _ _ hH₁ hH₃ e)
    have hl23 : lab (conjSub b H₀) ≠ lab (conjSub (a * b) H₀) :=
      fun e => hd23 (hinj _ _ hH₂ hH₃ e)
    have hcov : ∀ H : Subgroup G, IsHyp Ω H → x ∉ H → H = H₀ ∨ H = conjSub a H₀ ∨
        H = conjSub b H₀ ∨ H = conjSub (a * b) H₀ := by
      intro H hH hxH
      obtain ⟨k, hk, hkH⟩ := h.exists_conj_hyp_of_not_mem hK hxK hH₀ hH hx₀ hxH
      rcases hQ.nf k hk with e | e | e | e | e | e | e | e
      · rw [e, conjSub_one] at hkH
        exact Or.inl hkH.symm
      · rw [e] at hkH
        exact Or.inl (hkH.symm.trans (h.deq2_conj_eq_zGroup hH₀.1 hxD))
      · rw [e] at hkH
        exact Or.inr (Or.inl hkH.symm)
      · rw [e, conjSub_mul] at hkH
        exact Or.inr (Or.inl (hkH.symm.trans (h.deq2_conj_eq_zGroup hH₁.1 hxD)))
      · rw [e] at hkH
        exact Or.inr (Or.inr (Or.inl hkH.symm))
      · rw [e, conjSub_mul] at hkH
        exact Or.inr (Or.inr (Or.inl (hkH.symm.trans (h.deq2_conj_eq_zGroup hH₂.1 hxD))))
      · rw [e] at hkH
        exact Or.inr (Or.inr (Or.inr hkH.symm))
      · rw [e, conjSub_mul] at hkH
        exact Or.inr (Or.inr (Or.inr (hkH.symm.trans (h.deq2_conj_eq_zGroup hH₃.1 hxD))))
    have hsetT : Finset.univ.filter
        (fun i : Fin 7 => ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H) =
        {lab H₀, lab (conjSub a H₀), lab (conjSub b H₀), lab (conjSub (a * b) H₀)} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨H, hH, rfl, hxH⟩
        rcases hcov H hH hxH with e | e | e | e <;> simp [e]
      · rintro (e | e | e | e)
        · exact ⟨H₀, hH₀, e.symm, hx₀⟩
        · exact ⟨conjSub a H₀, hH₁, e.symm, hx₁⟩
        · exact ⟨conjSub b H₀, hH₂, e.symm, hx₂⟩
        · exact ⟨conjSub (a * b) H₀, hH₃, e.symm, hx₃⟩
    have hn1 : lab H₀ ∉ ({lab (conjSub a H₀), lab (conjSub b H₀), lab (conjSub (a * b) H₀)} :
        Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hl01, hl02, hl03⟩
    have hn2 : lab (conjSub a H₀) ∉ ({lab (conjSub b H₀), lab (conjSub (a * b) H₀)} :
        Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hl12, hl13⟩
    have hn3 : lab (conjSub b H₀) ∉ ({lab (conjSub (a * b) H₀)} : Finset (Fin 7)) := by
      simp only [Finset.mem_singleton]
      exact hl23
    have hprod : ∏ i ∈ Finset.univ.filter
        (fun i : Fin 7 => ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H), y i =
        y (lab H₀) * (y (lab (conjSub a H₀)) *
          (y (lab (conjSub b H₀)) * y (lab (conjSub (a * b) H₀)))) := by
      rw [hsetT, Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_insert hn3,
        Finset.prod_singleton]
    have hβx : deq2_coord y hy (Multiplicative.ofAdd fun i =>
        if ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H then (1 : ZMod 2) else 0) =
        ∏ i ∈ Finset.univ.filter
          (fun i : Fin 7 => ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H), y i := by
      rw [deq2_coord_apply, Finset.prod_filter]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [toAdd_ofAdd]
      split_ifs with hi
      · simp [show (1 : ZMod 2).val = 1 from rfl]
      · simp
    have hfl : flipVal (Lf x) (h.yElt H₀) = 1 := by
      rw [h.flipVal_yElt hH₀ hK hxK, if_neg hx₀]
    have hN := h.norm_identity hK hQ (h.yElt_mem_pCore hH₀)
    rw [hfl, if_pos (rfl : (1 : ZMod 2) = 1), h.yElt_conj hH₀ a, h.yElt_conj hH₀ b,
      h.yElt_conj hH₀ (a * b)] at hN
    simp only [mul_assoc] at hN
    rw [hβ, hβx, hprod, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hy_def, hy_def,
      hy_def, hy_def, hsH _ hH₀, hsH _ hH₁, hsH _ hH₂, hsH _ hH₃]
    exact hN.symm
  have hD_surj : ∀ d ∈ zGroup Ω, ∃ f, β f = d := by
    intro d hd
    by_cases hd1 : d = 1
    · exact ⟨1, by rw [map_one, hd1]⟩
    · exact ⟨_, (hzRel d hd hd1).symm⟩
  have hQ_surj : ∀ q ∈ pCore 2 G, ∃ f, β f = q := by
    intro q hq
    by_cases hΛ : deq2Lam Ω Lf q = 0
    · exact hD_surj q ((h.deq2_lam_eq_zero_iff hLf hq).mp hΛ)
    · obtain ⟨H, hH, hF⟩ := h.deq2_dual_eq_fh (h.deq2_lam_mem_dual hLf hq) hΛ
      have hyq : h.yElt H ∈ pCore 2 G := h.yElt_mem_pCore hH
      have hsum : deq2Lam Ω Lf (q * h.yElt H) = 0 := by
        rw [h.deq2_lam_mul hLf hq hyq, hLamY H hH, hF]
        funext x
        simp only [Pi.add_apply, Pi.zero_apply]
        exact deq2_zmod2_add_self _
      have hqD : q * h.yElt H ∈ zGroup Ω :=
        (h.deq2_lam_eq_zero_iff hLf ((pCore 2 G).mul_mem hq hyq)).mp hsum
      obtain ⟨f₁, hf₁⟩ := hD_surj _ hqD
      refine ⟨f₁ * Multiplicative.ofAdd (Pi.single (lab H) 1), ?_⟩
      rw [map_mul, hf₁, hsingle H hH, mul_assoc, h.pCore_mul_self _ hyq, mul_one]
  have hrange : β.range = pCore 2 G := by
    ext q
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      rw [hβ]
      exact (deq2_coord y hy f).2
    · intro hq
      exact hQ_surj q hq
  have hsurjQ : Function.Surjective (deq2_coord y hy) := by
    intro q
    obtain ⟨f, hf⟩ := hQ_surj q.1 q.2
    exact ⟨f, Subtype.ext ((hβ f).symm.trans hf)⟩
  have hcard := deq2_coord_card_ker y hy hsurjQ h.card_pCore_eq
  obtain ⟨r, hr, hr1, hker⟩ := deq2_coord_ker_eq y hy hcard
  have hstab : ∀ (g : G) (f : Multiplicative (Fin 7 → ZMod 2)), deq2_coord y hy f = 1 →
      deq2_coord y hy (Multiplicative.ofAdd fun j => f.toAdd ((σ g).symm j)) = 1 := by
    intro g f hf
    have e := deq2_coord_map y hy (cQ g) (σ g) (hφ g) f
    rw [hf, map_one] at e
    exact e.symm
  have hfix : ∀ (g : G) (j : Fin 7), r.toAdd ((σ g).symm j) = r.toAdd j := by
    intro g j
    rcases hker _ (hstab g r hr) with h1 | h1
    · exfalso
      apply hr1
      have h2 := congrArg Multiplicative.toAdd h1
      simp only [toAdd_ofAdd, toAdd_one] at h2
      apply toAdd_eq_zero.mp
      funext i
      have h3 := congrFun h2 (σ g i)
      simpa using h3
    · have h2 := congrArg Multiplicative.toAdd h1
      simp only [toAdd_ofAdd] at h2
      exact congrFun h2 j
  have htrans : ∀ i j : Fin 7, ∃ g : G, σ g i = j := by
    intro i j
    obtain ⟨g, hg⟩ := h.exists_conj_hyp (hHs i) (hHs j)
    refine ⟨g, ?_⟩
    have e := hconj g (Hs i) (hHs i)
    rw [hg, hlabs j, hlabs i] at e
    exact e.symm
  have hconst : ∀ i j : Fin 7, r.toAdd i = r.toAdd j := by
    intro i j
    obtain ⟨g, rfl⟩ := htrans i j
    have e := hfix g (σ g i)
    rw [Equiv.symm_apply_apply] at e
    exact e
  have hc1 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hR1 : r.toAdd = fun _ => 1 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, r.toAdd i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hr1
      apply toAdd_eq_zero.mp
      funext i
      exact hcon i
    funext j
    rw [hconst j i₀, hc1 _ hi₀]
  have hker_iff : ∀ f, β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1 := by
    intro f
    have e : β f = 1 ↔ deq2_coord y hy f = 1 := by
      rw [hβ]
      exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
    rw [e]
    constructor
    · intro hf
      rcases hker f hf with h1 | h1
      · exact Or.inl (by rw [h1, toAdd_one])
      · exact Or.inr (by rw [h1, hR1])
    · rintro (h1 | h1)
      · rw [show f = 1 from toAdd_eq_zero.mp h1, map_one]
      · have hfr : f = r := Multiplicative.toAdd.injective (h1.trans hR1.symm)
        rw [hfr]
        exact hr
  exact ⟨β, hrange, hker_iff, hconj_eq, hzRel⟩

open Classical in
structure Coords (Ω : Set (Subgroup G)) where
  lab : Subgroup G → Fin 7
  σ : G →* Equiv.Perm (Fin 7)
  β : Multiplicative (Fin 7 → ZMod 2) →* G
  lab_inj : ∀ H H' : Subgroup G, IsHyp Ω H → IsHyp Ω H' → lab H = lab H' → H = H'
  lab_surj : ∀ i : Fin 7, ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i
  lab_conj : ∀ (g : G) (H : Subgroup G), IsHyp Ω H → lab (conjSub g H) = σ g (lab H)
  σ_mem : ∀ g : G, σ g ∈ AE.l32
  line : ∀ x ∈ zGroup Ω, x ≠ 1 → ∃ ℓ ∈ AE.fanoLines, ∀ H : Subgroup G, IsHyp Ω H →
    (x ∈ H ↔ lab H ∈ ℓ)
  range_eq : β.range = pCore 2 G
  ker_eq : ∀ f : Multiplicative (Fin 7 → ZMod 2),
    β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1
  conj_eq : ∀ (g : G) (f : Multiplicative (Fin 7 → ZMod 2)),
    g * β f * g⁻¹ = β (Multiplicative.ofAdd fun i => f.toAdd ((σ g).symm i))
  zRel : ∀ x ∈ zGroup Ω, x ≠ 1 →
    x = β (Multiplicative.ofAdd fun i => if ∃ H : Subgroup G, IsHyp Ω H ∧ lab H = i ∧ x ∉ H
      then 1 else 0)

theorem exists_coords : Nonempty (Coords Ω) := by
  obtain ⟨lab, σ, h1, h2, h3, h4, h5⟩ := h.deq2_labelling
  obtain ⟨β, hr, hk, hc, hz⟩ := h.deq2_beta lab σ h1 h2 h3
  exact ⟨⟨lab, σ, β, h1, h2, h3, h4, h5, hr, hk, hc, hz⟩⟩

end DE2Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
