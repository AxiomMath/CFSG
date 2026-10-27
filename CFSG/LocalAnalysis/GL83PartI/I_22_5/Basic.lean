module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def cj (b : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj b).toMonoidHom

theorem mem_cj {b : G} {K : Subgroup G} {x : G} : x ∈ cj b K ↔ b⁻¹ * x * b ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : b⁻¹ * (b * y * b⁻¹) * b = y := by group
    simpa [MulAut.conj_apply, this] using hy
  · intro h
    exact ⟨b⁻¹ * x * b, h, by simp [MulAut.conj_apply]; group⟩

theorem mul_mem_cj {b : G} {K : Subgroup G} {x : G} (hx : x ∈ K) : b * x * b⁻¹ ∈ cj b K :=
  ⟨x, hx, rfl⟩

theorem cj_one (K : Subgroup G) : cj 1 K = K := by
  ext x; simp [mem_cj]

theorem cj_mul (b c : G) (K : Subgroup G) : cj (b * c) K = cj b (cj c K) := by
  ext x; simp [mem_cj, mul_assoc]

theorem cj_mono (b : G) {K L : Subgroup G} (h : K ≤ L) : cj b K ≤ cj b L :=
  Subgroup.map_mono h

theorem cj_inv_cj (b : G) (K : Subgroup G) : cj b⁻¹ (cj b K) = K := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_cj_inv (b : G) (K : Subgroup G) : cj b (cj b⁻¹ K) = K := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

theorem cj_eq_iff_mem_normalizer {b : G} {K : Subgroup G} :
    cj b K = K ↔ b ∈ Subgroup.normalizer (K : Set G) :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).symm

theorem cj_iSup {ι : Sort*} (b : G) (K : ι → Subgroup G) : cj b (⨆ i, K i) = ⨆ i, cj b (K i) :=
  Subgroup.map_iSup _ _

theorem cj_eq_of_comm {c : G} {K : Subgroup G} (h : ∀ x ∈ K, c * x = x * c) : cj c K = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show c * y * c⁻¹ ∈ K
    rw [h y hy]
    simpa using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    show c * x * c⁻¹ = x
    rw [h x hx]
    group

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hle : H ≤ Subgroup.normalizer (K : Set G) := fun h hh =>
    Subgroup.centralizer_le_normalizer (K : Set G)
      (Subgroup.mem_centralizer_iff.2 fun k hk => (hc h hh k hk).symm)
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right H K hle
  constructor
  · intro hx
    have hx' : x ∈ (↑(H ⊔ K) : Set G) := hx
    rw [hco] at hx'
    obtain ⟨h, hh, k, hk, rfl⟩ := hx'
    exact ⟨h, hh, k, hk, rfl⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk

theorem card_sup_of_commute_of_inf_eq_bot [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hd : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  have hf : Function.Injective (fun hk : H × K => ((hk.1 : G) * (hk.2 : G))) := by
    rintro ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ ⟨⟨h', hh'⟩, ⟨k', hk'⟩⟩ heq
    have hheq : h * k = h' * k' := heq
    have h1 : h'⁻¹ * h = k' * k⁻¹ := by
      calc h'⁻¹ * h = h'⁻¹ * (h * k) * k⁻¹ := by group
        _ = h'⁻¹ * (h' * k') * k⁻¹ := by rw [hheq]
        _ = k' * k⁻¹ := by group
    have hmem : h'⁻¹ * h ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem hh') hh, h1 ▸ K.mul_mem hk' (K.inv_mem hk)⟩
    rw [hd, Subgroup.mem_bot] at hmem
    have e1 : h = h' := (inv_mul_eq_one.1 hmem).symm
    have e2 : k = k' := by
      have : k' * k⁻¹ = 1 := by rw [← h1]; exact hmem
      exact (mul_inv_eq_one.1 this).symm
    subst e1; subst e2
    rfl
  have hr : (↑(H ⊔ K : Subgroup G) : Set G) =
      Set.range (fun hk : H × K => ((hk.1 : G) * (hk.2 : G))) := by
    ext x
    rw [SetLike.mem_coe, mem_sup_of_commute hc]
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, rfl⟩
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact ⟨h, h.2, k, k.2, rfl⟩
  have h1 : Nat.card (↑(H ⊔ K : Subgroup G) : Set G) =
      Nat.card (Set.range (fun hk : H × K => ((hk.1 : G) * (hk.2 : G)))) := by rw [hr]
  calc Nat.card (H ⊔ K : Subgroup G) = Nat.card (↑(H ⊔ K : Subgroup G) : Set G) := rfl
    _ = Nat.card (Set.range (fun hk : H × K => ((hk.1 : G) * (hk.2 : G)))) := h1
    _ = Nat.card (H × K) := Nat.card_range_of_injective hf
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

theorem comm_of_iSup {ι κ : Sort*} (X : ι → Subgroup G) (Y : κ → Subgroup G)
    (h : ∀ i j, ∀ x ∈ X i, ∀ y ∈ Y j, x * y = y * x) :
    ∀ x ∈ ⨆ i, X i, ∀ y ∈ ⨆ j, Y j, x * y = y * x := by
  intro x hx y hy
  have h1 : ∀ j, Y j ≤ Subgroup.centralizer ((⨆ i, X i : Subgroup G) : Set G) := by
    intro j y' hy'
    rw [Subgroup.mem_centralizer_iff]
    intro x' hx'
    have hle : (⨆ i, X i) ≤ Subgroup.centralizer ({y'} : Set G) := iSup_le fun i x'' hx'' => by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact (h i j x'' hx'' y' hy').symm
    have := hle hx'
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this y' rfl).symm
  have h2 : (⨆ j, Y j) ≤ Subgroup.centralizer ((⨆ i, X i : Subgroup G) : Set G) :=
    iSup_le h1
  exact (Subgroup.mem_centralizer_iff.1 (h2 hy) x hx)

section Elem

variable {p : ℕ}

theorem elem_comm {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem elem_mono {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem isPGroup_of_elem {E : Subgroup G} (hE : IsElemAbelian p E) : IsPGroup p E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

theorem exists_card_eq_pow [Fact p.Prime] [Finite G] {E : Subgroup G} (hE : IsElemAbelian p E) :
    ∃ k : ℕ, Nat.card E = p ^ k :=
  IsPGroup.iff_card.1 (isPGroup_of_elem hE)

theorem zpowers_commute {H : Subgroup G} {z : G} (hz : ∀ h ∈ H, h * z = z * h) :
    ∀ h ∈ H, ∀ k ∈ Subgroup.zpowers z, h * k = k * h := by
  intro h hh k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact ((Commute.zpow_right (hz h hh) n)).eq

theorem inf_zpowers_eq_bot [Fact p.Prime] {H : Subgroup G} {z : G} (hord : orderOf z = p)
    (hzH : z ∉ H) : H ⊓ Subgroup.zpowers z = ⊥ := by
  have hZcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hord]
  have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨hZcard ▸ Fact.out⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    (H.subgroupOf (Subgroup.zpowers z)) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.1 h
  · exfalso
    apply hzH
    have : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
        H.subgroupOf (Subgroup.zpowers z) := by rw [h]; trivial
    exact this

theorem zpow_mem_iff_dvd [Fact p.Prime] {H : Subgroup G} {z : G} (hord : orderOf z = p)
    (hzH : z ∉ H) (n : ℤ) : z ^ n ∈ H ↔ (p : ℤ) ∣ n := by
  constructor
  · intro h
    have h1 : z ^ n ∈ H ⊓ Subgroup.zpowers z := ⟨h, Subgroup.zpow_mem_zpowers z n⟩
    rw [inf_zpowers_eq_bot hord hzH, Subgroup.mem_bot] at h1
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  · intro h
    rw [← hord] at h
    rw [orderOf_dvd_iff_zpow_eq_one.1 h]
    exact H.one_mem

theorem card_sup_zpowers [Fact p.Prime] [Finite G] {B H : Subgroup G} (hB : IsElemAbelian p B)
    (hHB : H ≤ B) {z : G} (hz : z ∈ B) (hzH : z ∉ H) :
    Nat.card (H ⊔ Subgroup.zpowers z : Subgroup G) = p * Nat.card H := by
  have hz1 : z ≠ 1 := fun h => hzH (h ▸ H.one_mem)
  have hord : orderOf z = p := orderOf_eq_prime (hB.2 z hz) hz1
  have hZcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hord]
  have hc : ∀ h ∈ H, ∀ k ∈ Subgroup.zpowers z, h * k = k * h :=
    zpowers_commute fun h hh => elem_comm hB (hHB hh) hz
  have hd : H ⊓ Subgroup.zpowers z = ⊥ := inf_zpowers_eq_bot hord hzH
  rw [card_sup_of_commute_of_inf_eq_bot hc hd, hZcard, mul_comm]

end Elem

theorem exists_complement {p : ℕ} [Fact p.Prime] [Finite G] {B A : Subgroup G}
    (hB : IsElemAbelian p B) (hAB : A ≤ B) {b : G} (hb : b ∈ B) (hbA : b ∉ A) :
    ∃ B' : Subgroup G, A ≤ B' ∧ B' ≤ B ∧ b ∉ B' ∧ B ≤ B' ⊔ Subgroup.zpowers b := by
  classical
  let S : Set (Subgroup G) := {H | A ≤ H ∧ H ≤ B ∧ b ∉ H}
  obtain ⟨H, ⟨hAH, hHB, hbH⟩, hmax⟩ := (Set.toFinite S).exists_maximal ⟨A, le_rfl, hAB, hbA⟩
  refine ⟨H, hAH, hHB, hbH, fun x hx => ?_⟩
  by_contra hxM
  have hxH : x ∉ H := fun h => hxM (Subgroup.mem_sup_left h)
  have hH₁B : H ⊔ Subgroup.zpowers x ≤ B := sup_le hHB ((Subgroup.zpowers_le).2 hx)
  have hbH₁ : b ∈ H ⊔ Subgroup.zpowers x := by
    by_contra hbH₁
    have h1 : H ⊔ Subgroup.zpowers x ≤ H :=
      hmax ⟨hAH.trans le_sup_left, hH₁B, hbH₁⟩ le_sup_left
    exact hxH (h1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hle : H ⊔ Subgroup.zpowers b ≤ H ⊔ Subgroup.zpowers x :=
    sup_le le_sup_left ((Subgroup.zpowers_le).2 hbH₁)
  have hc1 := card_sup_zpowers hB hHB hb hbH
  have hc2 := card_sup_zpowers hB hHB hx hxH
  have heq : H ⊔ Subgroup.zpowers b = H ⊔ Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
  exact hxM (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem card_eq_of_complement {p : ℕ} [Fact p.Prime] [Finite G] {B B' : Subgroup G}
    (hB : IsElemAbelian p B) (hB'B : B' ≤ B) {b : G} (hb : b ∈ B) (hbB' : b ∉ B')
    (hsup : B ≤ B' ⊔ Subgroup.zpowers b) : Nat.card B = p * Nat.card B' := by
  have hle : B' ⊔ Subgroup.zpowers b ≤ B := sup_le hB'B ((Subgroup.zpowers_le).2 hb)
  have heq : B' ⊔ Subgroup.zpowers b = B := le_antisymm hle hsup
  rw [← heq]
  exact card_sup_zpowers hB hB'B hb hbB'

theorem quasisimple_nonabelian {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ x y : Q, x * y ≠ y * x := by
  by_contra h
  have hcomm : IsMulCommutative Q := ⟨⟨fun a b => by
    by_contra hne
    exact h ⟨a, b, hne⟩⟩⟩
  have hbot : commutator Q = ⊥ := commutator_eq_bot Q
  have htop : (⊤ : Subgroup Q) = ⊥ := by rw [← hQ.1]; exact hbot
  have hnt := CFSG.ComponentClassification.Quasisimple.nontrivial hQ
  have htriv : Subsingleton Q := ⟨fun x y => by
    have hx : x ∈ (⊥ : Subgroup Q) := htop ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup Q) := htop ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]⟩
  exact not_subsingleton Q htriv

theorem quasisimple_quotient_nonabelian {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ s t : Q ⧸ Subgroup.center Q, s * t ≠ t * s := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := quasisimple_nonabelian hQ
  have hcomm : ∀ s t : Q ⧸ Subgroup.center Q, s * t = t * s := fun s t => by
    by_contra hne
    exact h ⟨s, t, hne⟩
  have hcentral : ∀ a b : Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center Q := by
    intro a b
    have h1 : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : Q ⧸ Subgroup.center Q) = 1 := by
      have := commutatorElement_eq_one_iff_mul_comm.2
        (hcomm (QuotientGroup.mk a) (QuotientGroup.mk b))
      rw [commutatorElement_def] at this
      simpa using this
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [commutatorElement_def]
    exact hcentral a b
  rw [hQ.1] at hle
  have hx : x ∈ Subgroup.center Q := hle (Subgroup.mem_top x)
  exact hxy (Subgroup.mem_center_iff.1 hx y).symm

theorem endo_eq_id_of_central {Q : Type*} [Group Q] (hperf : commutator Q = ⊤) (φ : Q →* Q)
    (h : ∀ x, (φ x)⁻¹ * x ∈ Subgroup.center Q) : ∀ x, φ x = x := by
  have hfix : commutator Q ≤ MonoidHom.eqLocus φ (MonoidHom.id Q) := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    show φ (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹
    obtain ⟨c, hc⟩ : ∃ c, c = (φ a)⁻¹ * a := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = (φ b)⁻¹ * b := ⟨_, rfl⟩
    have hca : ∀ g, g * c = c * g := by rw [hc]; exact Subgroup.mem_center_iff.1 (h a)
    have hdb : ∀ g, g * d = d * g := by rw [hd]; exact Subgroup.mem_center_iff.1 (h b)
    have ea : φ a = a * c⁻¹ := by rw [hc]; group
    have eb : φ b = b * d⁻¹ := by rw [hd]; group
    have hcc : ∀ g, g * c⁻¹ = c⁻¹ * g := fun g => (Commute.inv_right (hca g)).eq
    have hdd : ∀ g, g * d⁻¹ = d⁻¹ * g := fun g => (Commute.inv_right (hdb g)).eq
    have e1 : φ a * φ b = (a * b) * (c⁻¹ * d⁻¹) := by
      rw [ea, eb]
      calc a * c⁻¹ * (b * d⁻¹) = a * (c⁻¹ * b) * d⁻¹ := by group
        _ = a * (b * c⁻¹) * d⁻¹ := by rw [hcc b]
        _ = (a * b) * (c⁻¹ * d⁻¹) := by group
    have e2 : φ b * φ a = (b * a) * (c⁻¹ * d⁻¹) := by
      rw [ea, eb]
      calc b * d⁻¹ * (a * c⁻¹) = b * (d⁻¹ * a) * c⁻¹ := by group
        _ = b * (a * d⁻¹) * c⁻¹ := by rw [hdd a]
        _ = b * a * (d⁻¹ * c⁻¹) := by group
        _ = (b * a) * (c⁻¹ * d⁻¹) := by rw [hcc d⁻¹]
    calc φ (a * b * a⁻¹ * b⁻¹) = (φ a * φ b) * (φ b * φ a)⁻¹ := by simp [map_mul, map_inv]; group
      _ = ((a * b) * (c⁻¹ * d⁻¹)) * ((b * a) * (c⁻¹ * d⁻¹))⁻¹ := by rw [e1, e2]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  intro x
  have : x ∈ MonoidHom.eqLocus φ (MonoidHom.id Q) := hfix (by rw [hperf]; exact Subgroup.mem_top x)
  exact this

end GL83.CompFam
