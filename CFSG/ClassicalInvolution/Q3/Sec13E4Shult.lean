module

public import CFSG.ClassicalInvolution.Q3.Sec13E4Swap
public import CFSG.Quasithin.Background.GoldschmidtShultThm

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

abbrev bar (K : Subgroup G) : Subgroup (G ⧸ pCore 2 G) :=
  K.map (QuotientGroup.mk' (pCore 2 G))

theorem comap_bar (K : Subgroup G) :
    (bar K).comap (QuotientGroup.mk' (pCore 2 G)) = K ⊔ pCore 2 G := by
  unfold bar
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

private theorem e4_mk_mem_bar_iff (K : Subgroup G) (g : G) :
    QuotientGroup.mk' (pCore 2 G) g ∈ bar K ↔ g ∈ K ⊔ pCore 2 G := by
  rw [← comap_bar K]
  exact Iff.rfl

private theorem e4_map_conj_bar (K : Subgroup G) (x : G) :
    (bar K).map (MulAut.conj (x : G ⧸ pCore 2 G)).toMonoidHom = bar (conjSub x K) := by
  unfold bar conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem e4_mem_normalizer_of_conjSub_eq {X : Type} [Group X] {n : X} {E : Subgroup X}
    (h : conjSub n E = E) : n ∈ Subgroup.normalizer (E : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : ∀ y, y ∈ E ↔ n⁻¹ * y * n ∈ E := fun y => by
    rw [← mem_conjSub_iff, h]
  rw [h1 (n * x * n⁻¹)]
  have : n⁻¹ * (n * x * n⁻¹) * n = x := by group
  rw [this]

private theorem e4_card_map_mk_mul (K N : Subgroup G) [N.Normal] :
    Nat.card (K.map (QuotientGroup.mk' N)) * Nat.card ↥(K ⊓ N) = Nat.card K := by
  let g : K →* G ⧸ N := (QuotientGroup.mk' N).domRestrict K
  have h1 : Nat.card g.range = g.ker.index := (Subgroup.index_ker g).symm
  have h2 : g.ker.index * Nat.card g.ker = Nat.card K := Subgroup.index_mul_card g.ker
  have h3 : g.ker = N.subgroupOf K := by
    rw [MonoidHom.ker_restrict, QuotientGroup.ker_mk']
  have h4 : g.range = K.map (QuotientGroup.mk' N) := MonoidHom.restrict_range K _
  have h5 : Nat.card (N.subgroupOf K) = Nat.card ↥(K ⊓ N) := by
    have := Subgroup.card_map_of_injective (K := N.subgroupOf K) (f := K.subtype)
      K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_comm] at this
    exact this.symm
  rw [← h4, h1, ← h5, ← h3]
  exact h2

private theorem e4_sq_eq_one_or {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hcard : Nat.card K = 8) (hnab : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) {k : G} (hk : k ∈ K) :
    k * k = 1 ∨ k * k = z := by
  have hord : orderOf k ∣ 2 ^ 3 := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
    rwa [Subgroup.orderOf_mk, hcard] at this
  have h4 : k ^ 4 = 1 := by
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    by_cases hm3 : m = 3
    · exfalso
      subst hm3
      obtain ⟨x, hx, y, hy, hxy⟩ := hnab
      have hKz : Subgroup.zpowers k = K :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk)
          (by rw [Nat.card_zpowers, hm', hcard]; norm_num)
      rw [← hKz, Subgroup.mem_zpowers_iff] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hxy (Commute.zpow_zpow_self k i j).eq
    · have hm2 : m ≤ 2 := by omega
      have h22 : orderOf k ∣ 4 := by
        rw [hm']
        exact (pow_dvd_pow 2 hm2).trans (by norm_num)
      exact orderOf_dvd_iff_pow_eq_one.mp h22
  have hsq : (k * k) * (k * k) = 1 := by
    have : (k * k) * (k * k) = k ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
    rw [this, h4]
  exact hz.unique (k * k) (K.mul_mem hk hk) hsq

private theorem e4_sq_eq_one_of_mem_inf {L : Subgroup G}
    (hcard : Nat.card ↥(L ⊓ pCore 2 G) ≤ 2) {c : G} (hc : c ∈ L) (hcQ : c ∈ pCore 2 G) :
    c * c = 1 := by
  have hmem : c ∈ L ⊓ pCore 2 G := ⟨hc, hcQ⟩
  have hdvd : orderOf c ∣ Nat.card ↥(L ⊓ pCore 2 G) := by
    have := orderOf_dvd_natCard (⟨c, hmem⟩ : ↥(L ⊓ pCore 2 G))
    rwa [Subgroup.orderOf_mk] at this
  have hle : orderOf c ∣ 2 := by
    have hpos : 0 < Nat.card ↥(L ⊓ pCore 2 G) := Nat.card_pos
    have : Nat.card ↥(L ⊓ pCore 2 G) = 1 ∨ Nat.card ↥(L ⊓ pCore 2 G) = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1] at hdvd
    · exact hdvd.trans (one_dvd 2)
    · exact hdvd
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp hle

private theorem e4_odd_card_fusionOddCore (H : Type) [Group H] [Finite H] :
    Odd (Nat.card (fusionOddCore H)) := by
  have e : fusionOddCore H = CFSG.pPrimeCore 2 H := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext N
    exact and_congr Iff.rfl Nat.coprime_two_left.symm
  rw [e]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem exists_partner {K : Subgroup G} (hK : K ∈ Ω) : ∃ J : Subgroup G, Paired Ω K J := by
  obtain ⟨A, B, hp⟩ := h.exists_paired
  obtain ⟨g, hg⟩ := h.thmD.trans A hp.1 K hK
  refine ⟨conjSub g B, ?_⟩
  rw [← hg]
  exact hp.conj h.thmD.hyp.conjInvariant g

theorem card_bar {K : Subgroup G} (hK : K ∈ Ω) : Nat.card (bar K) = 4 := by
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have hle := h.card_inf_pCore_le hK
  have hc2 : Nat.card ↥(K ⊓ pCore 2 G) = 2 := by
    have hpos : 0 < Nat.card ↥(K ⊓ pCore 2 G) := Nat.card_pos
    have hne : Nat.card ↥(K ⊓ pCore 2 G) ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      have hzmem : z ∈ K ⊓ pCore 2 G := ⟨hz.mem, h.mem_pCore hK hz⟩
      rw [h1, Subgroup.mem_bot] at hzmem
      exact hz.ne_one hzmem
    omega
  have hmul : Nat.card (bar K) * 2 = 8 := by
    have := e4_card_map_mk_mul K (pCore 2 G)
    rwa [h.card_eq hK, hc2] at this
  omega

theorem isElemAbelian_bar {K : Subgroup G} (hK : K ∈ Ω) : IsElemAbelian 2 (bar K) := by
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have hsq : ∀ x ∈ bar K, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : k * k ∈ pCore 2 G := by
      rcases e4_sq_eq_one_or hz (h.card_eq hK) (h.nonabelian hK) hk with h2 | h2
      · rw [h2]
        exact one_mem _
      · rw [h2]
        exact h.mem_pCore hK hz
    rw [pow_two, ← map_mul]
    exact (QuotientGroup.eq_one_iff (k * k)).mpr h1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hsq⟩
  apply Subtype.ext
  have h1 := hsq a.1 a.2
  have h2 := hsq b.1 b.2
  have h3 := hsq (a.1 * b.1) (Subgroup.mul_mem _ a.2 b.2)
  have ha' : a.1⁻¹ = a.1 := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h1)
  have hb' : b.1⁻¹ = b.1 := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h2)
  have hab' : (a.1 * b.1)⁻¹ = a.1 * b.1 := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h3)
  calc a.1 * b.1 = (a.1 * b.1)⁻¹ := hab'.symm
    _ = b.1 * a.1 := by rw [mul_inv_rev, ha', hb']

theorem bar_eq_of_paired {A B : Subgroup G} (hp : Paired Ω A B) : bar A = bar B := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, comap_bar]
    exact h.le_sup_pCore hp.symm
  · rw [Subgroup.map_le_iff_le_comap, comap_bar]
    exact h.le_sup_pCore hp

private theorem bar_eq_of_mem_normalizer {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {k : G}
    (hkK : k ∈ K) (hk1 : QuotientGroup.mk' (pCore 2 G) k ≠ 1)
    (hkN : k ∈ Subgroup.normalizer ((L ⊔ pCore 2 G : Subgroup G) : Set G)) : bar L = bar K := by
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have hkQ : k ∉ pCore 2 G := fun hkQ =>
    hk1 ((QuotientGroup.eq_one_iff k).mpr hkQ)
  have hksq : k * k ≠ 1 := by
    intro h1
    rcases hz.unique k hkK h1 with h2 | h2
    · exact hkQ (h2 ▸ one_mem _)
    · exact hkQ (h2 ▸ h.mem_pCore hK hz)
  have hk1' : k ≠ 1 := fun h1 => hkQ (h1 ▸ one_mem _)
  have hord : 2 < orderOf k := by
    have h0 : 0 < orderOf k := orderOf_pos k
    have h1 : orderOf k ≠ 1 := fun h1 => hk1' (orderOf_eq_one_iff.mp h1)
    have h2 : orderOf k ≠ 2 := fun h2 => hksq (by
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h2]))
    omega
  obtain ⟨L', hp⟩ := h.exists_partner hL
  have hLQ : IsPGroup 2 ↥(L ⊔ pCore 2 G) :=
    (h.isPGroup hL).to_sup_of_normal_right pCore_isPGroup
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers k) :=
    (h.isPGroup hK).to_le (Subgroup.zpowers_le.mpr hkK)
  have hT : IsPGroup 2 ↥(Subgroup.zpowers k ⊔ (L ⊔ pCore 2 G)) :=
    hzp.to_sup_of_normal_right' hLQ (Subgroup.zpowers_le.mpr hkN)
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  have hLS : L ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_right.trans hS)
  have hL'S : L' ≤ (S : Subgroup G) := (h.le_sup_pCore hp).trans (le_sup_right.trans hS)
  have hzS : Subgroup.zpowers k ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hc : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    have h1 : Nat.card ↥(Subgroup.zpowers k) ≤ Nat.card ↥(K ⊓ (S : Subgroup G)) :=
      Subgroup.card_le_of_le (le_inf (Subgroup.zpowers_le.mpr hkK) hzS)
    rw [Nat.card_zpowers] at h1
    omega
  rcases h.eq_or_eq_of_paired hp hLS hL'S hK hc with hKL | hKL
  · rw [hKL]
  · rw [hKL]
    exact h.bar_eq_of_paired hp

theorem eq_bar_of_normalizes {K : Subgroup G} (hK : K ∈ Ω) {v : G ⧸ pCore 2 G} (hv : v ∈ bar K)
    (hv1 : v ≠ 1) (g : G ⧸ pCore 2 G)
    (hg : v ∈ Subgroup.normalizer (((bar K).map (MulAut.conj g).toMonoidHom : Subgroup _) :
      Set (G ⧸ pCore 2 G))) :
    (bar K).map (MulAut.conj g).toMonoidHom = bar K := by
  obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [e4_map_conj_bar] at hg ⊢
  have hL : conjSub x K ∈ Ω := h.thmD.hyp.conjInvariant x K hK
  refine h.bar_eq_of_mem_normalizer hK hL hkK hv1 ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp hg (QuotientGroup.mk' (pCore 2 G) y)
  have e : QuotientGroup.mk' (pCore 2 G) k * QuotientGroup.mk' (pCore 2 G) y *
      (QuotientGroup.mk' (pCore 2 G) k)⁻¹ = QuotientGroup.mk' (pCore 2 G) (k * y * k⁻¹) := by
    simp
  rw [e, e4_mk_mem_bar_iff, e4_mk_mem_bar_iff] at h1
  exact h1

theorem shultHyp {K : Subgroup G} (hK : K ∈ Ω) :
    Quasithin.Shult.ShultI85Hyp (Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G))) (bar K) := by
  refine ⟨?_, ?_, Subgroup.le_normalizer, ?_, h.isElemAbelian_bar hK, ?_⟩
  · intro htop
    have hnorm : (bar K).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hnorm' : (K ⊔ pCore 2 G).Normal := by
      rw [← comap_bar K]
      exact hnorm.comap _
    obtain ⟨K', hp⟩ := h.exists_partner hK
    obtain ⟨L, hL, hLK, hLK'⟩ := h.exists_third hp
    obtain ⟨g, hg⟩ := h.thmD.trans K hK L hL
    have hle : L ≤ K ⊔ pCore 2 G := by
      rw [← hg]
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h1 := hnorm'.conj_mem _ (Subgroup.mem_sup_left hy) g
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rwa [e] at h1
    rcases h.eq_or_eq_of_le_sup hp hL hle with h1 | h1
    · exact hLK h1
    · exact hLK' h1
  · intro hbot
    have := h.card_bar hK
    rw [hbot, Subgroup.card_bot] at this
    omega
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  · intro v hv hv1
    have hvM : v ∈ Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G)) :=
      Subgroup.le_normalizer hv
    refine ⟨QuotientGroup.mk 1, ?_, ?_⟩
    · show v • (QuotientGroup.mk 1 : (G ⧸ pCore 2 G) ⧸
        Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G))) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by rw [mul_one]; exact Subgroup.inv_mem _ hvM)
    · intro c hc
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at hc
      have h1 := QuotientGroup.eq.mp hc
      have hw : y⁻¹ * v * y ∈ Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G)) := by
        have := Subgroup.inv_mem _ h1
        have e : ((v * y)⁻¹ * y)⁻¹ = y⁻¹ * v * y := by group
        rwa [e] at this
      have hg : v ∈ Subgroup.normalizer
          (((bar K).map (MulAut.conj y).toMonoidHom : Subgroup _) : Set (G ⧸ pCore 2 G)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        have hu := Subgroup.mem_normalizer_iff.mp hw (y⁻¹ * u * y)
        have e : (y⁻¹ * v * y) * (y⁻¹ * u * y) * (y⁻¹ * v * y)⁻¹ = y⁻¹ * (v * u * v⁻¹) * y := by
          group
        rw [e] at hu
        have key : ∀ t, t ∈ (bar K).map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * t * y ∈ bar K :=
          fun t => mem_conjSub_iff
        rw [key, key]
        exact hu
      have heq := h.eq_bar_of_normalizes hK hv hv1 y hg
      have hyN : y ∈ Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G)) :=
        e4_mem_normalizer_of_conjSub_eq heq
      exact QuotientGroup.eq.mpr (by rw [mul_one]; exact Subgroup.inv_mem _ hyN)

theorem normalClosure_bar {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.normalClosure (bar K : Set (G ⧸ pCore 2 G)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ pSpan Ω := by
    rw [h.thmD.gen]
    exact Subgroup.mem_top x
  have hle : pSpan Ω ≤ (Subgroup.normalClosure (bar K : Set (G ⧸ pCore 2 G))).comap
      (QuotientGroup.mk' (pCore 2 G)) := by
    refine pSpan_le fun L hL l hl => ?_
    obtain ⟨g, rfl⟩ := h.thmD.trans K hK L hL
    rw [mem_conjSub_iff] at hl
    have hmem : QuotientGroup.mk' (pCore 2 G) (g⁻¹ * l * g) ∈
        Subgroup.normalClosure (bar K : Set (G ⧸ pCore 2 G)) :=
      Subgroup.subset_normalClosure (Subgroup.mem_map_of_mem _ hl)
    have h1 := Subgroup.normalClosure_normal.conj_mem _ hmem (QuotientGroup.mk' (pCore 2 G) g)
    have e : QuotientGroup.mk' (pCore 2 G) g * QuotientGroup.mk' (pCore 2 G) (g⁻¹ * l * g) *
        (QuotientGroup.mk' (pCore 2 G) g)⁻¹ = QuotientGroup.mk' (pCore 2 G) l := by
      simp only [map_mul, map_inv]
      group
    rw [e] at h1
    exact h1
  exact hle hx

private theorem eq_one_of_mk_mem_center {y : G} (hy : Odd (orderOf y))
    (hc : QuotientGroup.mk' (pCore 2 G) y ∈ Subgroup.center (G ⧸ pCore 2 G)) : y = 1 := by
  obtain ⟨n, hn⟩ := hy
  have hyy : (y * y) ^ (n + 1) = y := by
    rw [← pow_two, ← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, ← hn,
      pow_orderOf_eq_one, one_mul]
  have hmk : ∀ w : G, QuotientGroup.mk' (pCore 2 G) (y * w * y⁻¹) =
      QuotientGroup.mk' (pCore 2 G) w := by
    intro w
    have h1 := (Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' (pCore 2 G) w)).symm
    simp only [map_mul, map_inv]
    rw [h1, mul_inv_cancel_right]
  have hcen : ∀ L ∈ Ω, ∀ l ∈ L, y * l = l * y := by
    intro L hL l hl
    obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hL
    obtain ⟨L', hp⟩ := h.exists_partner hL
    have hyN : ∀ w : G, w ∈ L ⊔ pCore 2 G ↔ y * w * y⁻¹ ∈ L ⊔ pCore 2 G := fun w => by
      rw [← e4_mk_mem_bar_iff L w, ← e4_mk_mem_bar_iff L (y * w * y⁻¹), hmk]
    have hconj_le : ∀ M : Subgroup G, M ≤ L ⊔ pCore 2 G → conjSub y M ≤ L ⊔ pCore 2 G := by
      intro M hM w hw
      rw [mem_conjSub_iff] at hw
      have h1 := (hyN (y⁻¹ * w * y)).mp (hM hw)
      have e : y * (y⁻¹ * w * y) * y⁻¹ = w := by group
      rwa [e] at h1
    have hL'le : L' ≤ L ⊔ pCore 2 G := h.le_sup_pCore hp
    have hyL : conjSub y L ∈ Ω := h.thmD.hyp.conjInvariant y L hL
    have hyL' : conjSub y L' ∈ Ω := h.thmD.hyp.conjInvariant y L' hp.2.1
    have h1 := h.eq_or_eq_of_le_sup hp hyL (hconj_le L le_sup_left)
    have h2 := h.eq_or_eq_of_le_sup hp hyL' (hconj_le L' hL'le)
    have hA : conjSub (y * y) L = L := by
      rw [conjSub_mul]
      rcases h1 with h1 | h1
      · rw [h1, h1]
      · rcases h2 with h2 | h2
        · rw [h1, h2]
        · exact absurd (conjSub_injective y (h1.trans h2.symm)) hp.2.2.1
    have hB : conjSub y L = L := by
      have hyy' : y * y ∈ Subgroup.normalizer (L : Set G) := e4_mem_normalizer_of_conjSub_eq hA
      have : y ∈ Subgroup.normalizer (L : Set G) := by
        rw [← hyy]
        exact Subgroup.pow_mem _ hyy' _
      exact conjSub_eq_of_mem_normalizer this
    have hLy : y * l * y⁻¹ ∈ L := by
      have := conj_mem_conjSub (n := y) hl
      rwa [hB] at this
    have hc1 : y * l * y⁻¹ * l⁻¹ ∈ L := L.mul_mem hLy (L.inv_mem hl)
    have hc2 : y * l * y⁻¹ * l⁻¹ ∈ pCore 2 G := by
      have h3 : QuotientGroup.mk' (pCore 2 G) (y * l * y⁻¹ * l⁻¹) = 1 := by
        rw [map_mul, map_inv, hmk, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h3
    obtain ⟨c, hcdef⟩ : ∃ c, c = y * l * y⁻¹ * l⁻¹ := ⟨_, rfl⟩
    rw [← hcdef] at hc1 hc2
    have hcc : c * c = 1 := e4_sq_eq_one_of_mem_inf (h.card_inf_pCore_le hL) hc1 hc2
    have hyl : y * l * y⁻¹ = c * l := by
      rw [hcdef]
      group
    have hyc : y * c * y⁻¹ = c := by
      rcases hz.unique c hc1 hcc with h3 | h3
      · rw [h3]
        group
      · rw [h3]
        exact hz.conj_eq hB
    have hcomm : y * y * l = l * (y * y) := by
      have e1 : y * y * l * (y * y)⁻¹ = y * (y * l * y⁻¹) * y⁻¹ := by group
      have e2 : y * (y * l * y⁻¹) * y⁻¹ = l := by
        rw [hyl]
        calc y * (c * l) * y⁻¹ = (y * c * y⁻¹) * (y * l * y⁻¹) := by group
          _ = c * (c * l) := by rw [hyc, hyl]
          _ = (c * c) * l := by rw [mul_assoc]
          _ = l := by rw [hcc, one_mul]
      exact mul_inv_eq_iff_eq_mul.mp (e1.trans e2)
    have hcm : Commute (y * y) l := hcomm
    have := (hcm.pow_left (n + 1)).eq
    rwa [hyy] at this
  have hle : pSpan Ω ≤ Subgroup.centralizer ({y} : Set G) := by
    refine pSpan_le fun L hL l hl => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hcen L hL l hl
  have hycen : y ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ pSpan Ω := by
      rw [h.thmD.gen]
      exact Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp (hle hg)) y rfl).symm
  rw [h.center] at hycen
  exact Subgroup.mem_bot.mp hycen

theorem eq_one_of_mem_center_of_odd {x : G ⧸ pCore 2 G} (hx : x ∈ Subgroup.center (G ⧸ pCore 2 G))
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₀).ne'
  have hord : orderOf (y₀ ^ (2 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) (by rw [hNm]; exact dvd_mul_right _ _),
      hNm]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hmk : QuotientGroup.mk' (pCore 2 G) (y₀ ^ (2 ^ a)) =
      (QuotientGroup.mk y₀ : G ⧸ pCore 2 G) ^ (2 ^ a) := by
    rw [map_pow]
    rfl
  have hc : QuotientGroup.mk' (pCore 2 G) (y₀ ^ (2 ^ a)) ∈ Subgroup.center (G ⧸ pCore 2 G) := by
    rw [hmk]
    exact Subgroup.pow_mem _ hx _
  have h1 : y₀ ^ (2 ^ a) = 1 := h.eq_one_of_mk_mem_center (by rw [hord]; exact hm) hc
  have h2 : (QuotientGroup.mk y₀ : G ⧸ pCore 2 G) ^ (2 ^ a) = 1 := by
    rw [← hmk, h1, map_one]
  have h3 : orderOf (QuotientGroup.mk y₀ : G ⧸ pCore 2 G) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h2
  have h4 : Nat.Coprime (orderOf (QuotientGroup.mk y₀ : G ⧸ pCore 2 G)) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_left.mpr hodd).symm
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h3)

theorem quot_cases
    {K : Subgroup G} (hK : K ∈ Ω) :
    (Nonempty (G ⧸ pCore 2 G ≃* PSL(2, GaloisField 2 2)) ∨
      Nonempty (G ⧸ pCore 2 G ≃* PSU3 2 2)) ∧
    ∃ P : Subgroup (G ⧸ pCore 2 G), IsSylowTwoOf P ⊤ ∧ Quasithin.Shult.IsOmegaOne (bar K) P := by
  have hS := Quasithin.Shult.shultI85Part1 (G ⧸ pCore 2 G)
    (Subgroup.normalizer (bar K : Set (G ⧸ pCore 2 G))) (bar K) (h.shultHyp hK)
  have hcl := h.normalClosure_bar hK
  have hcard := h.card_bar hK
  rcases hS with ⟨h2, -⟩ | ⟨f, hf, hQ, ⟨P, hP, hΩ⟩, -, -⟩
  · omega
  · have hf2 : f = 2 := by
      have h22 : (2 : ℕ) ^ f = 2 ^ 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) h22
    subst hf2
    rw [hcl] at hQ hP
    obtain ⟨-, hcen, hcases⟩ := hQ
    have hcen_bot : Subgroup.center ↥(⊤ : Subgroup (G ⧸ pCore 2 G)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ fusionOddCore ↥(⊤ : Subgroup (G ⧸ pCore 2 G)) := hcen ▸ hx
      have hxodd : Odd (orderOf x) := by
        have h1 := orderOf_dvd_natCard
          (⟨x, hx'⟩ : fusionOddCore ↥(⊤ : Subgroup (G ⧸ pCore 2 G)))
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat (e4_odd_card_fusionOddCore _) h1
      have hxc : (x : G ⧸ pCore 2 G) ∈ Subgroup.center (G ⧸ pCore 2 G) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, Subgroup.mem_top g⟩)
      have h1 := h.eq_one_of_mem_center_of_odd hxc (by rwa [Subgroup.orderOf_coe])
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    let e : ↥(⊤ : Subgroup (G ⧸ pCore 2 G)) ⧸ Subgroup.center ↥(⊤ : Subgroup (G ⧸ pCore 2 G)) ≃*
        G ⧸ pCore 2 G :=
      (QuotientGroup.quotientMulEquivOfEq hcen_bot).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    rcases hcases with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨a, ha, ha2, -⟩
    · exact ⟨Or.inl ⟨e.symm.trans φ⟩, P, hP, hΩ⟩
    · exact ⟨Or.inr ⟨e.symm.trans φ⟩, P, hP, hΩ⟩
    · omega

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
