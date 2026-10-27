module

public import CFSG.ClassicalInvolution.Q3.Sec13End18A
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

section Helpers

variable {Ω : Set (Subgroup G)}

private theorem e18b_comm (h : EndHyp Ω) (h9 : Perp9 Ω) {a b : G} (ha : a ∈ zGroup Ω)
    (hb : b ∈ zGroup Ω) : a * b = b * a :=
  h.zGroup_comm h9 a ha b hb

private theorem e18b_sq (h : EndHyp Ω) (h9 : Perp9 Ω) {a : G} (ha : a ∈ zGroup Ω) :
    a * a = 1 :=
  h.zGroup_mul_self h9 a ha

private theorem e18b_mem_zGroup {L : Subgroup G} {u : G} (hL : L ∈ Ω)
    (hu : IsUniqueInvolution L u) : u ∈ zGroup Ω :=
  Subgroup.subset_closure ⟨L, hL, hu⟩

private theorem e18b_zGroup_normal (hΩ : ConjInvariant Ω) : (zGroup Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : n ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, hL, hu⟩ := hx
    exact Subgroup.subset_closure ⟨conjSub g L, hΩ g L hL, hu.conj g⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (zGroup Ω).one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact (zGroup Ω).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (zGroup Ω).inv_mem hx

private theorem e18b_mem_zpowers_of_D_inf (h : EndHyp Ω) (h9 : Perp9 Ω) {K : Subgroup G}
    {z x : G} (hz : IsUniqueInvolution K z) (hxK : x ∈ K) (hxD : x ∈ zGroup Ω) :
    x ∈ Subgroup.zpowers z := by
  rcases hz.unique x hxK (e18b_sq h h9 hxD) with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers z

private theorem e18b_center (h : EndHyp Ω) {L : Subgroup G} {z c : G} (hL : L ∈ Ω)
    (hz : IsUniqueInvolution L z) (hc : c ∈ L) (hcc : ∀ y ∈ L, c * y = y * c) :
    c ∈ Subgroup.zpowers z := by
  rcases hz.unique c hc ((h.isQuatSub_of_mem hL).sq_eq_one_of_central hc hcc) with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers z

private theorem e18b_twin_inv {K L : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hL : L ∈ twinSet Ω K) : IsUniqueInvolution L z := by
  obtain ⟨-, w, hwK, hwL⟩ := hL
  have e : z = w := hz.eq hwK
  rw [e]
  exact hwL

private theorem e18b_conj_mem_twin (h : EndHyp Ω) (h9 : Perp9 Ω) {K L : Subgroup G} {z d : G}
    (hz : IsUniqueInvolution K z) (hd : d ∈ zGroup Ω) (hL : L ∈ twinSet Ω K) :
    conjSub d L ∈ twinSet Ω K := by
  have hLΩ : L ∈ Ω := by
    obtain ⟨h1, -⟩ := hL
    exact h1
  have hLz := e18b_twin_inv hz hL
  have hzD : z ∈ zGroup Ω := e18b_mem_zGroup hLΩ hLz
  have hdz : d * z = z * d := e18b_comm h h9 hd hzD
  have hz' : d * z * d⁻¹ = z := by rw [hdz, mul_inv_cancel_right]
  have hinv := hLz.conj d
  rw [hz'] at hinv
  exact ⟨h.thmD.hyp.conjInvariant d L hLΩ, z, hz, hinv⟩

private theorem e18b_self_mem_twin {K : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) : K ∈ twinSet Ω K :=
  ⟨hK, z, hz, hz⟩

private theorem e18b_dComm_mem_D (hN : (zGroup Ω).Normal) {d : G} (hd : d ∈ zGroup Ω) (k : G) :
    dComm d k ∈ zGroup Ω := by
  have e : dComm d k = d * (k * d⁻¹ * k⁻¹) := by unfold dComm; group
  rw [e]
  exact (zGroup Ω).mul_mem hd (hN.conj_mem d⁻¹ ((zGroup Ω).inv_mem hd) k)

private theorem e18b_dComm_mem_sup {K : Subgroup G} {s k : G} (hk : k ∈ K) :
    dComm s k ∈ K ⊔ conjSub s K := by
  have e : dComm s k = (s * k * s⁻¹) * k⁻¹ := by unfold dComm; group
  rw [e]
  exact (K ⊔ conjSub s K).mul_mem (Subgroup.mem_sup_right (conj_mem_conjSub hk))
    (Subgroup.mem_sup_left (K.inv_mem hk))

private theorem e18b_dComm_swap {K : Subgroup G} {s k k₁ : G}
    (hc : Commutes K (conjSub s K)) (hk : k ∈ K) (hk₁ : k₁ ∈ K) :
    dComm (dComm s k) k₁ = k⁻¹ * k₁ * k * k₁⁻¹ := by
  have hP : s * k * s⁻¹ ∈ conjSub s K := conj_mem_conjSub hk
  have hx : k⁻¹ * k₁ * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hk) hk₁) hk
  have hcom : (k⁻¹ * k₁ * k) * (s * k * s⁻¹) = (s * k * s⁻¹) * (k⁻¹ * k₁ * k) :=
    hc _ hx _ hP
  calc dComm (dComm s k) k₁ = (s * k * s⁻¹) * (k⁻¹ * k₁ * k) * (s * k * s⁻¹)⁻¹ * k₁⁻¹ := by
        simp only [dComm]; group
    _ = (k⁻¹ * k₁ * k) * (s * k * s⁻¹) * (s * k * s⁻¹)⁻¹ * k₁⁻¹ := by rw [← hcom]
    _ = k⁻¹ * k₁ * k * k₁⁻¹ := by group

private theorem e18b_q8_comm {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    i⁻¹ * j * i * j⁻¹ = z ∧ j⁻¹ * i * j * i⁻¹ = z := by
  have hij : i * j = z * (j * i) := by
    calc i * j = (z * z) * (i * j) := by rw [hQ.inv.sq, one_mul]
      _ = z * (z * (i * j)) := by group
      _ = z * (j * i) := by rw [hQ.comm]
  refine ⟨?_, ?_⟩
  · calc i⁻¹ * j * i * j⁻¹ = i⁻¹ * (j * i) * j⁻¹ := by group
      _ = i⁻¹ * (z * (i * j)) * j⁻¹ := by rw [hQ.comm]
      _ = i⁻¹ * (i * i * (i * j)) * j⁻¹ := by rw [hQ.sq_i]
      _ = i * i := by group
      _ = z := hQ.sq_i
  · calc j⁻¹ * i * j * i⁻¹ = j⁻¹ * (i * j) * i⁻¹ := by group
      _ = j⁻¹ * (z * (j * i)) * i⁻¹ := by rw [hij]
      _ = j⁻¹ * (j * j * (j * i)) * i⁻¹ := by rw [hQ.sq_j]
      _ = j * j := by group
      _ = z := hQ.sq_j

private theorem e18b_zpowers_one_or {z x : G} (hz2 : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · left
    rw [hm, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

private theorem e18b_comm_of_one_or {z x y : G} (hx : x = 1 ∨ x = z) (hy : y = 1 ∨ y = z) :
    x * y = y * x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp

private theorem e18b_centralizer_le_normalizer (K : Subgroup G) :
    Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  have hx' := Subgroup.mem_centralizer_iff.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have e : x * n * x⁻¹ = n := by
      rw [← hx' n hn]
      group
    rw [e]
    exact hn
  · intro hn
    have e3 : x⁻¹ * (x * n * x⁻¹) * x = x * n * x⁻¹ := by
      calc x⁻¹ * (x * n * x⁻¹) * x = x⁻¹ * ((x * n * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * n * x⁻¹)) := by rw [hx' _ hn]
        _ = x * n * x⁻¹ := by group
    have key : n = x * n * x⁻¹ := by
      calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
        _ = x * n * x⁻¹ := e3
    rw [key]
    exact hn

private theorem e18b_sup_le_normalizer {K K' : Subgroup G} (hc : Commutes K K') :
    K ⊔ K' ≤ Subgroup.normalizer (K : Set G) := by
  refine sup_le (fun k hk => Subgroup.le_normalizer hk) (fun k' hk' => ?_)
  apply e18b_centralizer_le_normalizer K
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact hc k hk k' hk'

private theorem e18b_mem_sup_decomp {K K' : Subgroup G} (hc : Commutes K K') {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  let P : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, k₁', hk₁', rfl⟩ ⟨k₂, hk₂, k₂', hk₂', rfl⟩
        refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
        have e := hc k₂ hk₂ k₁' hk₁'
        calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
          _ = k₁ * (k₂ * k₁') * k₂' := by rw [← e]
          _ = k₁ * k₂ * (k₁' * k₂') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, k', hk', rfl⟩
        refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
        have e := hc k hk k' hk'
        calc (k * k')⁻¹ = k'⁻¹ * k⁻¹ := by group
          _ = k⁻¹ * k'⁻¹ := by
            have e' : (k' * k)⁻¹ = (k * k')⁻¹ := by rw [e]
            rw [mul_inv_rev, mul_inv_rev] at e'
            exact e'.symm }
  have hle : K ⊔ K' ≤ P := by
    refine sup_le (fun k hk => ⟨k, hk, 1, K'.one_mem, by simp⟩)
      (fun k' hk' => ⟨1, K.one_mem, k', hk', by simp⟩)
  exact hle hx

private theorem e18b_commute_of_gens {K : Subgroup G} {z i j c : G} (hQ : Q8Data K z i j)
    (hcz : c * z = z * c) (hci : c * i = i * c) (hcj : c * j = j * c) :
    c ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcz' : Commute c z := hcz
  have hci' : Commute c i := hci
  have hcj' : Commute c j := hcj
  have hcy : Commute c y := by
    rcases hQ.nf y hy with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
    · exact Commute.one_right c
    · exact hcz'
    · exact hci'
    · exact hcz'.mul_right hci'
    · exact hcj'
    · exact hcz'.mul_right hcj'
    · exact hci'.mul_right hcj'
    · exact hcz'.mul_right (hci'.mul_right hcj')
  exact hcy.symm.eq

private theorem e18b_exists_pair {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j)
    (hN : (zGroup Ω).Normal) {s : G} (hs : s ∈ zGroup Ω) (hc : Commutes K (conjSub s K))
    {p q : G} (hp : p = 1 ∨ p = z) (hq : q = 1 ∨ q = z) :
    ∃ d ∈ zGroup Ω ⊓ (K ⊔ conjSub s K), dComm d i = p ∧ dComm d j = q := by
  obtain ⟨hq1, hq2⟩ := e18b_q8_comm hQ
  have hbi : dComm s i ∈ zGroup Ω ⊓ (K ⊔ conjSub s K) :=
    Subgroup.mem_inf.mpr ⟨e18b_dComm_mem_D hN hs i, e18b_dComm_mem_sup hQ.mem_i⟩
  have hbj : dComm s j ∈ zGroup Ω ⊓ (K ⊔ conjSub s K) :=
    Subgroup.mem_inf.mpr ⟨e18b_dComm_mem_D hN hs j, e18b_dComm_mem_sup hQ.mem_j⟩
  have vii : dComm (dComm s i) i = 1 := by
    rw [e18b_dComm_swap hc hQ.mem_i hQ.mem_i]; group
  have vij : dComm (dComm s i) j = z := by
    rw [e18b_dComm_swap hc hQ.mem_i hQ.mem_j]; exact hq1
  have vji : dComm (dComm s j) i = z := by
    rw [e18b_dComm_swap hc hQ.mem_j hQ.mem_i]; exact hq2
  have vjj : dComm (dComm s j) j = 1 := by
    rw [e18b_dComm_swap hc hQ.mem_j hQ.mem_j]; group
  have hNj : dComm s j ∈ Subgroup.normalizer (K : Set G) :=
    e18b_sup_le_normalizer hc (e18b_dComm_mem_sup hQ.mem_j)
  rcases hp with h1 | h1 <;> rcases hq with h2 | h2
  · exact ⟨1, Subgroup.one_mem _, by rw [h1]; unfold dComm; group,
      by rw [h2]; unfold dComm; group⟩
  · exact ⟨dComm s i, hbi, by rw [vii, h1], by rw [vij, h2]⟩
  · exact ⟨dComm s j, hbj, by rw [vji, h1], by rw [vjj, h2]⟩
  · refine ⟨dComm s j * dComm s i, (zGroup Ω ⊓ (K ⊔ conjSub s K)).mul_mem hbj hbi, ?_, ?_⟩
    · rw [dComm_mul_left hQ.inv hNj (Or.inl vii), vii, vji, one_mul, h1]
    · rw [dComm_mul_left hQ.inv hNj (Or.inr vij), vij, vjj, mul_one, h2]

private theorem e18b_card_eq_four_mul (h : EndHyp Ω) (h9 : Perp9 Ω) (hN : (zGroup Ω).Normal)
    {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) {S : Subgroup G}
    (hSD : S ≤ zGroup Ω) (hSN : S ≤ Subgroup.normalizer (K : Set G))
    (hsurj : ∀ p q : G, (p = 1 ∨ p = z) → (q = 1 ∨ q = z) →
      ∃ d ∈ S, dComm d i = p ∧ dComm d j = q) :
    Nat.card ↥S = 4 * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) := by
  have hzz := hQ.inv.sq
  have hz1 := hQ.inv.ne_one
  have hcomm : ∀ d ∈ S, ∀ k ∈ K, dComm d k ∈ Subgroup.zpowers z := fun d hd k hk =>
    e18b_mem_zpowers_of_D_inf h h9 hQ.inv (dComm_mem (hSN hd) hk)
      (e18b_dComm_mem_D hN (hSD hd) k)
  have hpi : ∀ d ∈ S, dComm d i ∈ Subgroup.zpowers z := fun d hd => hcomm d hd i hQ.mem_i
  have hpj : ∀ d ∈ S, dComm d j ∈ Subgroup.zpowers z := fun d hd => hcomm d hd j hQ.mem_j
  have hmul_i : ∀ a b : S, dComm ((a * b : S) : G) i = dComm (a : G) i * dComm (b : G) i := by
    intro a b
    rw [Subgroup.coe_mul, dComm_mul_left hQ.inv (hSN a.2)
      (e18b_zpowers_one_or hzz (hpi b b.2))]
    exact e18b_comm_of_one_or (e18b_zpowers_one_or hzz (hpi b b.2))
      (e18b_zpowers_one_or hzz (hpi a a.2))
  have hmul_j : ∀ a b : S, dComm ((a * b : S) : G) j = dComm (a : G) j * dComm (b : G) j := by
    intro a b
    rw [Subgroup.coe_mul, dComm_mul_left hQ.inv (hSN a.2)
      (e18b_zpowers_one_or hzz (hpj b b.2))]
    exact e18b_comm_of_one_or (e18b_zpowers_one_or hzz (hpj b b.2))
      (e18b_zpowers_one_or hzz (hpj a a.2))
  let f₁ : S →* Subgroup.zpowers z :=
    MonoidHom.mk' (fun d => ⟨dComm (d : G) i, hpi d d.2⟩) (fun a b => Subtype.ext (hmul_i a b))
  let f₂ : S →* Subgroup.zpowers z :=
    MonoidHom.mk' (fun d => ⟨dComm (d : G) j, hpj d d.2⟩) (fun a b => Subtype.ext (hmul_j a b))
  let φ : S →* Subgroup.zpowers z × Subgroup.zpowers z := f₁.prod f₂
  have hφ : ∀ d : S, φ d = 1 ↔ dComm (d : G) i = 1 ∧ dComm (d : G) j = 1 := by
    intro d
    constructor
    · intro hd
      exact ⟨congrArg (fun x => ((x.1 : Subgroup.zpowers z) : G)) hd,
        congrArg (fun x => ((x.2 : Subgroup.zpowers z) : G)) hd⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hker : φ.ker = (S ⊓ Subgroup.centralizer (K : Set G)).subgroupOf S := by
    ext d
    rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨d.2, ?_⟩
      have hc : ∀ k ∈ K, dComm (d : G) k = 1 ∨ dComm (d : G) k = z := fun k hk =>
        e18b_zpowers_one_or hzz (hcomm d d.2 k hk)
      have hall : ∀ k ∈ K, dComm (d : G) k = 1 := fun k hk =>
        dComm_eq_one_of_gens hQ (hSN d.2) hc h1 h2 hk
      exact Subgroup.mem_centralizer_iff.mpr (fun k hk =>
        (dComm_eq_one_iff.mp (hall k hk)).symm)
    · rintro ⟨-, hC⟩
      exact ⟨dComm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp hC i hQ.mem_i).symm,
        dComm_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mp hC j hQ.mem_j).symm⟩
  have hcard_ker : Nat.card ↥φ.ker = Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    obtain ⟨d, hd, e1, e2⟩ :=
      hsurj p q (e18b_zpowers_one_or hzz hp) (e18b_zpowers_one_or hzz hq)
    exact ⟨⟨d, hd⟩, Prod.ext (Subtype.ext e1) (Subtype.ext e2)⟩
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurjφ
  have hidx := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, card_zpowers_prod_eq_four hzz hz1,
    hcard_ker] at hidx
  rw [← hidx]
  ring

private theorem e18b_mul_normalizer {K : Subgroup G}
    (hN : (zGroup Ω ⊓ Subgroup.normalizer (K : Set G)).relIndex (zGroup Ω) = 2)
    (hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a)
    (hsq : ∀ a ∈ zGroup Ω, a * a = 1)
    {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω)
    (hxN : x ∉ Subgroup.normalizer (K : Set G)) (hyN : y ∉ Subgroup.normalizer (K : Set G)) :
    x * y ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨a, ha, -, hall⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hN
  have hxa : x * a ∈ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
    (hall x hx).resolve_right (fun h => hxN (Subgroup.mem_inf.mp h).2)
  have hya : y * a ∈ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
    (hall y hy).resolve_right (fun h => hyN (Subgroup.mem_inf.mp h).2)
  have e : (x * a) * (y * a) = x * y := by
    calc (x * a) * (y * a) = x * (a * y) * a := by group
      _ = x * (y * a) * a := by rw [hcomm a ha y hy]
      _ = x * y * (a * a) := by group
      _ = x * y := by rw [hsq a ha, mul_one]
  have hmem := (zGroup Ω ⊓ Subgroup.normalizer (K : Set G)).mul_mem hxa hya
  rw [e] at hmem
  exact (Subgroup.mem_inf.mp hmem).2

private theorem e18b_alg (a1 a2 a3 b1 b2 b3 : G) (h21 : a2 * b1 = b1 * a2)
    (h31 : a3 * b1 = b1 * a3) (h32 : a3 * b2 = b2 * a3) :
    a1 * b1 * (a2 * b2) * (a3 * b3) = a1 * a2 * a3 * (b1 * b2 * b3) := by
  calc a1 * b1 * (a2 * b2) * (a3 * b3) = a1 * (b1 * a2) * b2 * (a3 * b3) := by group
    _ = a1 * (a2 * b1) * b2 * (a3 * b3) := by rw [← h21]
    _ = a1 * a2 * b1 * (b2 * a3) * b3 := by group
    _ = a1 * a2 * b1 * (a3 * b2) * b3 := by rw [← h32]
    _ = a1 * a2 * (b1 * a3) * b2 * b3 := by group
    _ = a1 * a2 * (a3 * b1) * b2 * b3 := by rw [← h31]
    _ = a1 * a2 * a3 * (b1 * b2 * b3) := by group

private theorem e18b_triple_hom {A₁ A₂ A₃ : Subgroup G}
    (hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a)
    (h1 : A₁ ≤ zGroup Ω) (h2 : A₂ ≤ zGroup Ω) (h3 : A₃ ≤ zGroup Ω) :
    ∃ ψ : (↥A₁ × ↥A₂ × ↥A₃) →* G, ∀ x, ψ x = (x.1 : G) * (x.2.1 : G) * (x.2.2 : G) := by
  refine ⟨MonoidHom.mk' (fun x => (x.1 : G) * (x.2.1 : G) * (x.2.2 : G)) ?_, fun x => rfl⟩
  intro x y
  simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
  exact e18b_alg _ _ _ _ _ _ (hcomm _ (h2 x.2.1.2) _ (h1 y.1.2))
    (hcomm _ (h3 x.2.2.2) _ (h1 y.1.2)) (hcomm _ (h3 x.2.2.2) _ (h2 y.2.1.2))

private theorem e18b_key4 (h : EndHyp Ω) {z : G} {L₁ L₂ L₃ L₄ : Subgroup G}
    (m₂ : L₂ ∈ Ω) (m₃ : L₃ ∈ Ω) (m₄ : L₄ ∈ Ω)
    (z₂ : IsUniqueInvolution L₂ z) (z₃ : IsUniqueInvolution L₃ z)
    (z₄ : IsUniqueInvolution L₄ z)
    (c12 : Commutes L₁ L₂) (c13 : Commutes L₁ L₃) (c14 : Commutes L₁ L₄)
    (c23 : Commutes L₂ L₃) (c24 : Commutes L₂ L₄) (c34 : Commutes L₃ L₄)
    {w₁ w₂ w₃ w₄ : G} (h₁ : w₁ ∈ L₁) (h₂ : w₂ ∈ L₂) (h₃ : w₃ ∈ L₃) (h₄ : w₄ ∈ L₄)
    (hw : w₁ * w₂ * w₃ * w₄ = 1) :
    w₂ ∈ Subgroup.zpowers z ∧ w₃ ∈ Subgroup.zpowers z ∧ w₄ ∈ Subgroup.zpowers z := by
  have hw2 : w₂ = w₁⁻¹ * (w₃ * w₄)⁻¹ := by
    calc w₂ = w₁⁻¹ * (w₁ * w₂ * w₃ * w₄) * (w₃ * w₄)⁻¹ := by group
      _ = w₁⁻¹ * (w₃ * w₄)⁻¹ := by rw [hw, mul_one]
  have hw3 : w₃ = (w₁ * w₂)⁻¹ * w₄⁻¹ := by
    calc w₃ = (w₁ * w₂)⁻¹ * (w₁ * w₂ * w₃ * w₄) * w₄⁻¹ := by group
      _ = (w₁ * w₂)⁻¹ * w₄⁻¹ := by rw [hw, mul_one]
  have hw4 : w₄ = (w₁ * w₂ * w₃)⁻¹ := by
    calc w₄ = (w₁ * w₂ * w₃)⁻¹ * (w₁ * w₂ * w₃ * w₄) := by group
      _ = (w₁ * w₂ * w₃)⁻¹ := by rw [hw, mul_one]
  have cen2 : ∀ y ∈ L₂, y * w₂ = w₂ * y := by
    intro y hy
    have cy1 : Commute y w₁ := (c12 w₁ h₁ y hy).symm
    have cy3 : Commute y w₃ := c23 y hy w₃ h₃
    have cy4 : Commute y w₄ := c24 y hy w₄ h₄
    have hc : Commute y w₂ := by
      rw [hw2]
      exact (cy1.inv_right).mul_right ((cy3.mul_right cy4).inv_right)
    exact hc
  have cen3 : ∀ y ∈ L₃, y * w₃ = w₃ * y := by
    intro y hy
    have cy1 : Commute y w₁ := (c13 w₁ h₁ y hy).symm
    have cy2 : Commute y w₂ := (c23 w₂ h₂ y hy).symm
    have cy4 : Commute y w₄ := c34 y hy w₄ h₄
    have hc : Commute y w₃ := by
      rw [hw3]
      exact ((cy1.mul_right cy2).inv_right).mul_right cy4.inv_right
    exact hc
  have cen4 : ∀ y ∈ L₄, y * w₄ = w₄ * y := by
    intro y hy
    have cy1 : Commute y w₁ := (c14 w₁ h₁ y hy).symm
    have cy2 : Commute y w₂ := (c24 w₂ h₂ y hy).symm
    have cy3 : Commute y w₃ := (c34 w₃ h₃ y hy).symm
    have hc : Commute y w₄ := by
      rw [hw4]
      exact ((cy1.mul_right cy2).mul_right cy3).inv_right
    exact hc
  exact ⟨e18b_center h m₂ z₂ h₂ (fun y hy => (cen2 y hy).symm),
    e18b_center h m₃ z₃ h₃ (fun y hy => (cen3 y hy).symm),
    e18b_center h m₄ z₄ h₄ (fun y hy => (cen4 y hy).symm)⟩

private theorem e18b_triple (h : EndHyp Ω) {K K₂ K₃ K₄ : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (m₂ : K₂ ∈ Ω) (m₃ : K₃ ∈ Ω) (m₄ : K₄ ∈ Ω)
    (z₂ : IsUniqueInvolution K₂ z) (z₃ : IsUniqueInvolution K₃ z)
    (z₄ : IsUniqueInvolution K₄ z)
    (c12 : Commutes K K₂) (c13 : Commutes K K₃) (c14 : Commutes K K₄)
    (c23 : Commutes K₂ K₃) (c24 : Commutes K₂ K₄) (c34 : Commutes K₃ K₄)
    {t₂ t₃ t₄ : G} (ht₂ : t₂ ∈ K ⊔ K₂) (ht₃ : t₃ ∈ K ⊔ K₃) (ht₄ : t₄ ∈ K ⊔ K₄)
    (ht : t₂ * t₃ * t₄ = 1) : t₂ ∈ K ∧ t₃ ∈ K ∧ t₄ ∈ K := by
  obtain ⟨a₂, ha₂, c₂, hc₂, rfl⟩ := e18b_mem_sup_decomp c12 ht₂
  obtain ⟨a₃, ha₃, c₃, hc₃, rfl⟩ := e18b_mem_sup_decomp c13 ht₃
  obtain ⟨a₄, ha₄, c₄, hc₄, rfl⟩ := e18b_mem_sup_decomp c14 ht₄
  have e1 : c₂ * a₃ = a₃ * c₂ := (c12 a₃ ha₃ c₂ hc₂).symm
  have e2 : c₂ * a₄ = a₄ * c₂ := (c12 a₄ ha₄ c₂ hc₂).symm
  have e3 : c₃ * a₄ = a₄ * c₃ := (c13 a₄ ha₄ c₃ hc₃).symm
  have chain : a₂ * c₂ * (a₃ * c₃) * (a₄ * c₄) = (a₂ * a₃ * a₄) * (c₂ * c₃ * c₄) := by
    calc a₂ * c₂ * (a₃ * c₃) * (a₄ * c₄) = a₂ * (c₂ * a₃) * c₃ * (a₄ * c₄) := by group
      _ = a₂ * (a₃ * c₂) * c₃ * (a₄ * c₄) := by rw [e1]
      _ = a₂ * a₃ * (c₂ * (c₃ * a₄)) * c₄ := by group
      _ = a₂ * a₃ * (c₂ * (a₄ * c₃)) * c₄ := by rw [e3]
      _ = a₂ * a₃ * ((c₂ * a₄) * c₃) * c₄ := by group
      _ = a₂ * a₃ * ((a₄ * c₂) * c₃) * c₄ := by rw [e2]
      _ = (a₂ * a₃ * a₄) * (c₂ * c₃ * c₄) := by group
  have hre : (a₂ * a₃ * a₄) * c₂ * c₃ * c₄ = 1 := by
    rw [chain] at ht
    simpa only [mul_assoc] using ht
  have hA : a₂ * a₃ * a₄ ∈ K := K.mul_mem (K.mul_mem ha₂ ha₃) ha₄
  obtain ⟨hz2, hz3, hz4⟩ := e18b_key4 h m₂ m₃ m₄ z₂ z₃ z₄ c12 c13 c14 c23 c24 c34 hA hc₂ hc₃ hc₄
    hre
  have hzK : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.mpr hz.mem
  exact ⟨K.mul_mem ha₂ (hzK hz2), K.mul_mem ha₃ (hzK hz3), K.mul_mem ha₄ (hzK hz4)⟩

end Helpers

namespace End18

namespace Hyp

variable {Ω : Set (Subgroup G)} (H : Hyp Ω)
include H

theorem conjSub_mem_twinSet {K : Subgroup G} (hK : K ∈ Ω) {d : G} (hd : d ∈ zGroup Ω) :
    conjSub d K ∈ twinSet Ω K := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  exact e18b_conj_mem_twin H.endHyp H.perp9 hz hd (e18b_self_mem_twin hK hz)

theorem exists_swap {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ J ∈ Ω, ∃ s : G, IsUniqueInvolution J s ∧ conjSub s K ≠ K := by
  by_contra hcon
  push_neg at hcon
  have hle : zGroup Ω ≤ eGroup Ω K := by
    unfold zGroup
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨J, hJ, hu⟩
    exact (H.mem_eGroup_iff_normalizes hK hJ hu).mpr
      (mem_normalizer_iff_conjSub_eq.mpr (hcon J hJ u hu))
  exact H.ne K hK (le_antisymm hle (H.endHyp.eGroup_le_zGroup hK))

theorem card_dZero {K : Subgroup G} (hK : K ∈ Ω) {s : G} (hs : s ∈ zGroup Ω)
    (hsK : conjSub s K ≠ K) : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) = 8 := by
  obtain ⟨z, i, j, hQ⟩ := H.endHyp.exists_q8Data hK
  have hK' : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hKt : K ∈ twinSet Ω K := e18b_self_mem_twin hK hQ.inv
  have hc : Commutes K (conjSub s K) := (H.sup_twin hQ.inv hKt hK' (Ne.symm hsK)).1
  have hN : (zGroup Ω).Normal := e18b_zGroup_normal H.endHyp.thmD.hyp.conjInvariant
  have hC := e18b_card_eq_four_mul H.endHyp H.perp9 hN hQ
    (S := zGroup Ω ⊓ (K ⊔ conjSub s K)) inf_le_left
    (fun _ hx => e18b_sup_le_normalizer hc (Subgroup.mem_inf.mp hx).2)
    (fun p q hp hq => e18b_exists_pair hQ hN hs hc hp hq)
  have hzD : z ∈ zGroup Ω := e18b_mem_zGroup hK hQ.inv
  have hzi : z * i = i * z := by rw [← hQ.sq_i]; group
  have hzj : z * j = j * z := by rw [← hQ.sq_j]; group
  have hT : zGroup Ω ⊓ (K ⊔ conjSub s K) ⊓ Subgroup.centralizer (K : Set G) =
      Subgroup.zpowers z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hA, hxC⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxD, hxS⟩ := Subgroup.mem_inf.mp hA
      obtain ⟨k, hk, k', hk', rfl⟩ := e18b_mem_sup_decomp hc hxS
      have hk'C : k' ∈ Subgroup.centralizer (K : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun y hy => hc y hy k' hk')
      have hkC : k ∈ Subgroup.centralizer (K : Set G) := by
        have h2 := (Subgroup.centralizer (K : Set G)).mul_mem hxC
          ((Subgroup.centralizer (K : Set G)).inv_mem hk'C)
        simpa using h2
      have hkzp : k ∈ Subgroup.zpowers z :=
        e18b_center H.endHyp hK hQ.inv hk (fun y hy =>
          (Subgroup.mem_centralizer_iff.mp hkC y hy).symm)
      have hkD : k ∈ zGroup Ω := (Subgroup.zpowers_le.mpr hzD) hkzp
      have hk'D : k' ∈ zGroup Ω := by
        have h3 := (zGroup Ω).mul_mem ((zGroup Ω).inv_mem hkD) hxD
        simpa using h3
      have hk'zp : k' ∈ Subgroup.zpowers z :=
        e18b_mem_zpowers_of_D_inf H.endHyp H.perp9 (e18b_twin_inv hQ.inv hK') hk' hk'D
      exact (Subgroup.zpowers z).mul_mem hkzp hk'zp
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzD, Subgroup.mem_sup_left hQ.inv.mem⟩, ?_⟩
      exact e18b_commute_of_gens hQ rfl hzi hzj
  rw [hC, hT, card_zpowers_of_involution hQ.inv.sq hQ.inv.ne_one]

private theorem e18b_four_twins_false {K : Subgroup G} (hK : K ∈ Ω) {s y : G} (hs : s ∈ zGroup Ω)
    (hy : y ∈ zGroup Ω) (hsN : s ∉ Subgroup.normalizer (K : Set G))
    (hyN : y ∉ Subgroup.normalizer (K : Set G))
    (hsyN : s * y ∉ Subgroup.normalizer (K : Set G)) : False := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hsy : s * y ∈ zGroup Ω := (zGroup Ω).mul_mem hs hy
  have hcomm_sy : s * y = y * s := e18b_comm H.endHyp H.perp9 hs hy
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := fun a ha b hb =>
    e18b_comm H.endHyp H.perp9 ha hb
  have hs_ne : conjSub s K ≠ K := fun e => hsN (mem_normalizer_iff_conjSub_eq.mpr e)
  have hy_ne : conjSub y K ≠ K := fun e => hyN (mem_normalizer_iff_conjSub_eq.mpr e)
  have hsy_ne : conjSub (s * y) K ≠ K := fun e => hsyN (mem_normalizer_iff_conjSub_eq.mpr e)
  have hKt : K ∈ twinSet Ω K := e18b_self_mem_twin hK hz
  have hK2 : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hs
  have hK3 : conjSub y K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hy
  have hK4 : conjSub (s * y) K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hsy
  have h23 : conjSub s K ≠ conjSub y K := by
    intro e
    apply hsyN
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, ← e, ← conjSub_mul,
      e18b_sq H.endHyp H.perp9 hs, conjSub_one]
  have h24 : conjSub s K ≠ conjSub (s * y) K := by
    intro e
    apply hy_ne
    apply conjSub_injective s
    rw [← conjSub_mul]
    exact e.symm
  have h34 : conjSub y K ≠ conjSub (s * y) K := by
    intro e
    apply hs_ne
    apply conjSub_injective y
    rw [← conjSub_mul, ← hcomm_sy]
    exact e.symm
  have c12 : Commutes K (conjSub s K) := (H.sup_twin hz hKt hK2 (Ne.symm hs_ne)).1
  have c13 : Commutes K (conjSub y K) := (H.sup_twin hz hKt hK3 (Ne.symm hy_ne)).1
  have c14 : Commutes K (conjSub (s * y) K) := (H.sup_twin hz hKt hK4 (Ne.symm hsy_ne)).1
  have c23 : Commutes (conjSub s K) (conjSub y K) := (H.sup_twin hz hK2 hK3 h23).1
  have c24 : Commutes (conjSub s K) (conjSub (s * y) K) := (H.sup_twin hz hK2 hK4 h24).1
  have c34 : Commutes (conjSub y K) (conjSub (s * y) K) := (H.sup_twin hz hK3 hK4 h34).1
  have hT2 : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) = 8 := H.card_dZero hK hs hs_ne
  have hT3 : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub y K)) = 8 := H.card_dZero hK hy hy_ne
  have hT4 : Nat.card ↥(zGroup Ω ⊓ (K ⊔ conjSub (s * y) K)) = 8 := H.card_dZero hK hsy hsy_ne
  obtain ⟨ψ, hψ⟩ := e18b_triple_hom hcomm (fun _ hx => (Subgroup.mem_inf.mp hx).1)
    (fun _ hx => (Subgroup.mem_inf.mp hx).1) (fun _ hx => (Subgroup.mem_inf.mp hx).1)
  have hsup2 : K ⊔ conjSub s K ≤ pSpan (twinSet Ω K) := sup_le (le_pSpan hKt) (le_pSpan hK2)
  have hsup3 : K ⊔ conjSub y K ≤ pSpan (twinSet Ω K) := sup_le (le_pSpan hKt) (le_pSpan hK3)
  have hsup4 : K ⊔ conjSub (s * y) K ≤ pSpan (twinSet Ω K) :=
    sup_le (le_pSpan hKt) (le_pSpan hK4)
  have hrangeLe : ψ.range ≤ pSpan (twinSet Ω K) := by
    rintro _ ⟨x, rfl⟩
    rw [hψ]
    exact (pSpan (twinSet Ω K)).mul_mem ((pSpan (twinSet Ω K)).mul_mem
      (hsup2 (Subgroup.mem_inf.mp x.1.2).2) (hsup3 (Subgroup.mem_inf.mp x.2.1.2).2))
      (hsup4 (Subgroup.mem_inf.mp x.2.2.2).2)
  have hrangeD : ψ.range ≤ zGroup Ω := by
    rintro _ ⟨x, rfl⟩
    rw [hψ]
    exact (zGroup Ω).mul_mem ((zGroup Ω).mul_mem (Subgroup.mem_inf.mp x.1.2).1
      (Subgroup.mem_inf.mp x.2.1.2).1) (Subgroup.mem_inf.mp x.2.2.2).1
  have hrange32 : Nat.card ↥ψ.range ≤ 32 :=
    H.card_abelian_le_span hK hrangeLe (fun a ha b hb => hcomm a (hrangeD ha) b (hrangeD hb))
  have hkerZ : ∀ x : (↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) × ↥(zGroup Ω ⊓ (K ⊔ conjSub y K)) ×
      ↥(zGroup Ω ⊓ (K ⊔ conjSub (s * y) K))), ψ x = 1 →
      (x.1 : G) ∈ Subgroup.zpowers z ∧ (x.2.1 : G) ∈ Subgroup.zpowers z ∧
        (x.2.2 : G) ∈ Subgroup.zpowers z := by
    intro x hx
    rw [hψ] at hx
    obtain ⟨m2, m3, m4⟩ := e18b_triple H.endHyp hz hK2.1 hK3.1 hK4.1
      (e18b_twin_inv hz hK2) (e18b_twin_inv hz hK3) (e18b_twin_inv hz hK4)
      c12 c13 c14 c23 c24 c34 (Subgroup.mem_inf.mp x.1.2).2 (Subgroup.mem_inf.mp x.2.1.2).2
      (Subgroup.mem_inf.mp x.2.2.2).2 hx
    exact ⟨e18b_mem_zpowers_of_D_inf H.endHyp H.perp9 hz m2 (Subgroup.mem_inf.mp x.1.2).1,
      e18b_mem_zpowers_of_D_inf H.endHyp H.perp9 hz m3 (Subgroup.mem_inf.mp x.2.1.2).1,
      e18b_mem_zpowers_of_D_inf H.endHyp H.perp9 hz m4 (Subgroup.mem_inf.mp x.2.2.2).1⟩
  have hzz := hz.sq
  have hz1 := hz.ne_one
  have hker8 : Nat.card ↥ψ.ker ≤ 8 := by
    have hinj : Function.Injective (fun x : ↥ψ.ker =>
        ((⟨(x.1.1 : G), (hkerZ x.1 (MonoidHom.mem_ker.mp x.2)).1⟩ : ↥(Subgroup.zpowers z)),
          (⟨(x.1.2.1 : G), (hkerZ x.1 (MonoidHom.mem_ker.mp x.2)).2.1⟩ : ↥(Subgroup.zpowers z)),
          (⟨(x.1.2.2 : G), (hkerZ x.1 (MonoidHom.mem_ker.mp x.2)).2.2⟩ :
            ↥(Subgroup.zpowers z)))) := by
      rintro ⟨⟨a, b, c⟩, hx⟩ ⟨⟨a', b', c'⟩, hy⟩ hxy
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      have ea : a = a' := Subtype.ext h1
      have eb : b = b' := Subtype.ext h2
      have ec : c = c' := Subtype.ext h3
      subst ea eb ec
      rfl
    have hcardT : Nat.card (↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) ×
        ↥(Subgroup.zpowers z)) = 8 := by
      rw [Nat.card_prod, Nat.card_prod, card_zpowers_of_involution hzz hz1]
    rw [← hcardT]
    exact Nat.card_le_card_of_injective _ hinj
  have hdom : Nat.card (↥(zGroup Ω ⊓ (K ⊔ conjSub s K)) × ↥(zGroup Ω ⊓ (K ⊔ conjSub y K)) ×
      ↥(zGroup Ω ⊓ (K ⊔ conjSub (s * y) K))) = 512 := by
    rw [Nat.card_prod, Nat.card_prod, hT2, hT3, hT4]
  have hsplit := Subgroup.card_ker_mul_card_range ψ
  rw [hdom] at hsplit
  have hmul := Nat.mul_le_mul hker8 hrange32
  rw [hsplit] at hmul
  norm_num at hmul

theorem relIndex_inf_normalizer {K : Subgroup G} (hK : K ∈ Ω) :
    (zGroup Ω ⊓ Subgroup.normalizer (K : Set G)).relIndex (zGroup Ω) = 2 := by
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := e18b_mem_zGroup hJ hs
  have hsN : s ∉ Subgroup.normalizer (K : Set G) :=
    fun h => hsK (mem_normalizer_iff_conjSub_eq.mp h)
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨s, hsD, fun h => hsN (Subgroup.mem_inf.mp h).2, fun b hb => ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hbs, hbN⟩ := hcon
  have hbsD : b * s ∈ zGroup Ω := (zGroup Ω).mul_mem hb hsD
  have hbN' : b ∉ Subgroup.normalizer (K : Set G) := fun h => hbN (Subgroup.mem_inf.mpr ⟨hb, h⟩)
  have hsbN' : s * b ∉ Subgroup.normalizer (K : Set G) := by
    intro h
    apply hbs
    apply Subgroup.mem_inf.mpr ⟨hbsD, ?_⟩
    rw [← e18b_comm H.endHyp H.perp9 hsD hb]
    exact h
  exact e18b_four_twins_false H hK hsD hb hsN hbN' hsbN'

theorem zGroup_inf_normalizer_eq {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ twinSet Ω K) :
    zGroup Ω ⊓ Subgroup.normalizer (K : Set G) = zGroup Ω ⊓ Subgroup.normalizer (K' : Set G) := by
  have hN1 := H.relIndex_inf_normalizer hK
  have hN2 := H.relIndex_inf_normalizer hK'.1
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := fun a ha b hb =>
    e18b_comm H.endHyp H.perp9 ha hb
  have hsq : ∀ a ∈ zGroup Ω, a * a = 1 := fun a ha => e18b_sq H.endHyp H.perp9 ha
  have hmain : ∀ x ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u},
      x ∈ zGroup Ω ∧
        (x ∈ Subgroup.normalizer (K : Set G) ↔ x ∈ Subgroup.normalizer (K' : Set G)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨J, hJ, hu'⟩ := hu
      refine ⟨Subgroup.subset_closure ⟨J, hJ, hu'⟩, ?_⟩
      rw [← H.mem_eGroup_iff_normalizes hK hJ hu', ← H.mem_eGroup_iff_normalizes hK'.1 hJ hu',
        H.endHyp.eGroup_eq_of_mem_twinSet hK hK']
    | one =>
      exact ⟨(zGroup Ω).one_mem, ⟨fun _ => Subgroup.one_mem _, fun _ => Subgroup.one_mem _⟩⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨hA, hA'⟩ := iha
      obtain ⟨hB, hB'⟩ := ihb
      refine ⟨(zGroup Ω).mul_mem hA hB, ?_⟩
      by_cases hAN : a ∈ Subgroup.normalizer (K : Set G)
      · by_cases hBN : b ∈ Subgroup.normalizer (K : Set G)
        · exact ⟨fun _ => Subgroup.mul_mem _ (hA'.mp hAN) (hB'.mp hBN),
            fun _ => Subgroup.mul_mem _ hAN hBN⟩
        · have hBN' : b ∉ Subgroup.normalizer (K' : Set G) := fun h => hBN (hB'.mpr h)
          have h1 : a * b ∉ Subgroup.normalizer (K : Set G) :=
            fun h => hBN ((Subgroup.mul_mem_cancel_left _ hAN).mp h)
          have h2 : a * b ∉ Subgroup.normalizer (K' : Set G) :=
            fun h => hBN' ((Subgroup.mul_mem_cancel_left _ (hA'.mp hAN)).mp h)
          exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      · by_cases hBN : b ∈ Subgroup.normalizer (K : Set G)
        · have hAN' : a ∉ Subgroup.normalizer (K' : Set G) := fun h => hAN (hA'.mpr h)
          have h1 : a * b ∉ Subgroup.normalizer (K : Set G) :=
            fun h => hAN ((Subgroup.mul_mem_cancel_right _ hBN).mp h)
          have h2 : a * b ∉ Subgroup.normalizer (K' : Set G) :=
            fun h => hAN' ((Subgroup.mul_mem_cancel_right _ (hB'.mp hBN)).mp h)
          exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
        · have hAN' : a ∉ Subgroup.normalizer (K' : Set G) := fun h => hAN (hA'.mpr h)
          have hBN' : b ∉ Subgroup.normalizer (K' : Set G) := fun h => hBN (hB'.mpr h)
          have h1 := e18b_mul_normalizer hN1 hcomm hsq hA hB hAN hBN
          have h2 := e18b_mul_normalizer hN2 hcomm hsq hA hB hAN' hBN'
          exact ⟨fun _ => h2, fun _ => h1⟩
    | inv a _ iha =>
      obtain ⟨hA, hA'⟩ := iha
      exact ⟨(zGroup Ω).inv_mem hA, by simpa only [Subgroup.inv_mem_iff] using hA'⟩
  have key : ∀ d ∈ zGroup Ω,
      (d ∈ Subgroup.normalizer (K : Set G) ↔ d ∈ Subgroup.normalizer (K' : Set G)) :=
    fun d hd => (hmain d hd).2
  ext d
  constructor
  · intro hd
    obtain ⟨hD, hN⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨hD, (key d hD).mp hN⟩
  · intro hd
    obtain ⟨hD, hN⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨hD, (key d hD).mpr hN⟩

theorem exists_twin_involution {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ τ : Equiv.Perm ↥(twinSet Ω K), (∀ L, τ L ≠ L) ∧ τ * τ = 1 ∧
      ∀ d ∈ zGroup Ω,
        (∀ L : ↥(twinSet Ω K), conjSub d (L : Subgroup G) = (L : Subgroup G)) ∨
        (∀ L : ↥(twinSet Ω K), conjSub d (L : Subgroup G) = ((τ L : ↥(twinSet Ω K)) : Subgroup G))
    := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := e18b_mem_zGroup hJ hs
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := fun a ha b hb =>
    e18b_comm H.endHyp H.perp9 ha hb
  have hsq : ∀ a ∈ zGroup Ω, a * a = 1 := fun a ha => e18b_sq H.endHyp H.perp9 ha
  have hsN : s ∉ Subgroup.normalizer (K : Set G) :=
    fun h => hsK (mem_normalizer_iff_conjSub_eq.mp h)
  have hN1 := H.relIndex_inf_normalizer hK
  let f : ↥(twinSet Ω K) → ↥(twinSet Ω K) := fun L =>
    ⟨conjSub s (L : Subgroup G), e18b_conj_mem_twin H.endHyp H.perp9 hz hsD L.2⟩
  have hff : ∀ L, f (f L) = L := by
    intro L
    apply Subtype.ext
    show conjSub s (conjSub s (L : Subgroup G)) = (L : Subgroup G)
    rw [← conjSub_mul, e18b_sq H.endHyp H.perp9 hsD, conjSub_one]
  let τ : Equiv.Perm ↥(twinSet Ω K) :=
    { toFun := f, invFun := f, left_inv := hff, right_inv := hff }
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro L hL
    have hLe : conjSub s (L : Subgroup G) = (L : Subgroup G) := congrArg Subtype.val hL
    have hLN : s ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_conjSub_eq.mpr hLe
    have hmem : s ∈ zGroup Ω ⊓ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨hsD, hLN⟩
    rw [← H.zGroup_inf_normalizer_eq hK L.2] at hmem
    exact hsN (Subgroup.mem_inf.mp hmem).2
  · apply Equiv.ext
    intro L
    exact hff L
  · intro d hd
    by_cases hdN : d ∈ Subgroup.normalizer (K : Set G)
    · left
      intro L
      have hdL : d ∈ zGroup Ω ⊓ Subgroup.normalizer (L : Set G) := by
        rw [← H.zGroup_inf_normalizer_eq hK L.2]
        exact Subgroup.mem_inf.mpr ⟨hd, hdN⟩
      exact mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp hdL).2
    · right
      intro L
      have hsdN : s * d ∈ Subgroup.normalizer (K : Set G) :=
        e18b_mul_normalizer hN1 hcomm hsq hsD hd hsN hdN
      have hmem : s * d ∈ zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
        Subgroup.mem_inf.mpr ⟨(zGroup Ω).mul_mem hsD hd, hsdN⟩
      rw [H.zGroup_inf_normalizer_eq hK L.2] at hmem
      have hsdL : conjSub (s * d) (L : Subgroup G) = (L : Subgroup G) :=
        mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp hmem).2
      have e : d = s * (s * d) := by
        rw [← mul_assoc, e18b_sq H.endHyp H.perp9 hsD, one_mul]
      show conjSub d (L : Subgroup G) = conjSub s (L : Subgroup G)
      rw [e, conjSub_mul, hsdL]

theorem card_inf_centralizer_mul_eight {K : Subgroup G} (hK : K ∈ Ω) :
    Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) * 8 = Nat.card ↥(zGroup Ω) := by
  obtain ⟨z, i, j, hQ⟩ := H.endHyp.exists_q8Data hK
  obtain ⟨J, hJ, s, hs, hsK⟩ := H.exists_swap hK
  have hsD : s ∈ zGroup Ω := e18b_mem_zGroup hJ hs
  have hK' : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet hK hsD
  have hKt : K ∈ twinSet Ω K := e18b_self_mem_twin hK hQ.inv
  have hc : Commutes K (conjSub s K) := (H.sup_twin hQ.inv hKt hK' (Ne.symm hsK)).1
  have hN : (zGroup Ω).Normal := e18b_zGroup_normal H.endHyp.thmD.hyp.conjInvariant
  have hC := e18b_card_eq_four_mul H.endHyp H.perp9 hN hQ
    (S := zGroup Ω ⊓ Subgroup.normalizer (K : Set G)) inf_le_left inf_le_right
    (fun p q hp hq => by
      obtain ⟨d, hd, e1, e2⟩ := e18b_exists_pair hQ hN hsD hc hp hq
      exact ⟨d, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hd).1,
        e18b_sup_le_normalizer hc (Subgroup.mem_inf.mp hd).2⟩, e1, e2⟩)
  have hI : zGroup Ω ⊓ Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer (K : Set G) =
      zGroup Ω ⊓ Subgroup.centralizer (K : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr (e18b_centralizer_le_normalizer K)]
  have hrel := H.relIndex_inf_normalizer hK
  have hcard := Subgroup.relIndex_mul_card (H := zGroup Ω ⊓ Subgroup.normalizer (K : Set G))
    (K := zGroup Ω)
  rw [hrel, inf_eq_left.mpr inf_le_left] at hcard
  rw [hI] at hC
  rw [← hcard, hC]
  ring

end Hyp

end End18

end CFSG.ClassicalInvolution.Q3.Sec13
