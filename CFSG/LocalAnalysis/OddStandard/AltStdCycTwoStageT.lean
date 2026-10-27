module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.OddStandard.AltStdSecWreathJ
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup AltStdBal AltStdSec AltStdSec.Wreath

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

private theorem stageT_wconfig (hn : 8 ≤ n) (d : Cyc L Q z) {H : Subgroup G}
    (hH : WreathPair L z n H) : WConfig H z := by
  obtain ⟨e⟩ := hH.iso
  refine ⟨d.mul_self, fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
  · exact hH.comm a ha (z * b * z⁻¹) ⟨b, hb, by simp [MulAut.conj_apply]⟩
  · refine eq_one_of_mem_of_mem_centralizer e (by omega) ha ?_
    rw [mem_centralizer_iff]
    intro c' hc'
    exact hH.comm c' hc' a ⟨b, hb, by rw [hab]; simp [MulAut.conj_apply]⟩

private theorem stageT_z_not_mem (hn : 8 ≤ n) (d : Cyc L Q z) {H : Subgroup G}
    (hH : WreathPair L z n H) (c : WConfig H z) {T₁ : Subgroup G} (hT : T₁ ≤ H) :
    z ∉ prodSub c T₁ hT := by
  obtain ⟨e⟩ := hH.iso
  rintro ⟨a, ha, b, hb, hz⟩
  have hcent : ∀ c' ∈ H, c' * a = a * c' ∧ c' * b = b * c' := by
    intro c' hc'
    have hl : Phi z c' c' ∈ L := by
      have : Phi z c' c' ∈ (L : Set G) := by
        rw [hH.diag]
        exact ⟨c', hc', rfl⟩
      exact this
    have h1 := mem_centralizer_iff.1 (d.le d.mem) _ hl
    have h1' : Phi z c' c' * Phi z a b = Phi z a b * Phi z c' c' := by
      rw [← hz]
      exact h1
    have h2 := c.Phi_mul (a := c') (b := c') (a' := a) (b' := b) (hT ha) hc'
    have h3 := c.Phi_mul (a := a) (b := b) (a' := c') (b' := c') hc' (hT hb)
    rw [h2, h3] at h1'
    exact c.Phi_inj (mul_mem hc' (hT ha)) (mul_mem hc' (hT hb)) (mul_mem (hT ha) hc')
      (mul_mem (hT hb) hc') h1'
  have hn4 : 4 ≤ n := by omega
  have ha1 : a = 1 := eq_one_of_mem_of_mem_centralizer e hn4 (hT ha)
    (mem_centralizer_iff.2 fun c' hc' => (hcent c' hc').1)
  have hb1 : b = 1 := eq_one_of_mem_of_mem_centralizer e hn4 (hT hb)
    (mem_centralizer_iff.2 fun c' hc' => (hcent c' hc').2)
  have hz1 : z = 1 := by
    rw [hz, ha1, hb1]
    simp [Phi]
  have := d.order
  rw [hz1, orderOf_one] at this
  omega

omit [Finite G] in
private theorem stageT_exists_diagPre {H : Subgroup G} (hH : WreathPair L z n H)
    (c : WConfig H z) {P : Subgroup G} (hPL : P ≤ L) {p : G} (hp : p ∈ P) :
    ∃ a ∈ diagPre c P, Phi z a a = p := by
  have hpL : p ∈ (L : Set G) := hPL hp
  rw [hH.diag] at hpL
  obtain ⟨a, haH, rfl⟩ := hpL
  exact ⟨a, ⟨haH, hp⟩, rfl⟩

private theorem stageT_false_of_index_two (hS : StandardSetting G L) {N : Subgroup G} [N.Normal]
    (hN : N.index = 2) : False := by
  have hsimple := hS.simple
  have hnonab := hS.nonab
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h1 | h1
  · rw [h1, Subgroup.index_bot] at hN
    have := isCyclic_of_prime_card (α := G) hN
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h1, Subgroup.index_top] at hN
    exact absurd hN (by norm_num)

private theorem stageT_false (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) {H : Subgroup G}
    (hH : WreathPair L z n H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hH.iso
  set c := stageT_wconfig hn d hH
  obtain ⟨P₀⟩ : Nonempty (Sylow 2 L) := inferInstance
  set P₀' : Subgroup G := (P₀ : Subgroup L).map L.subtype
  have hP₀'L : P₀' ≤ L := Subgroup.map_subtype_le _
  have hP₀'p : IsPGroup 2 P₀' := P₀.isPGroup'.map L.subtype
  set T₁ := diagPre c P₀'
  have hT₁ : T₁ ≤ H := diagPre_le c P₀'
  have hT₁p : IsPGroup 2 T₁ := c.isPGroup_diagPre hP₀'p
  set T := prodSub c T₁ hT₁
  have hTn : ∀ x ∈ T, z * x * z⁻¹ ∈ T := fun x hx => c.z_mem_prodSub hT₁ hx
  have hTp : IsPGroup 2 T := c.isPGroup_prodSub hT₁ hT₁p
  have hz2 : orderOf z = 2 := d.order
  have hzz : z * z = 1 := d.mul_self
  set S := Ssub z hzz T hTn
  have hSp : IsPGroup 2 S := isPGroup_Ssub z hzz hz2 T hTn hTp
  have hzT : z ∉ T := stageT_z_not_mem hn d hH c hT₁
  have hzS : z ∈ S := z_mem_Ssub z hzz T hTn
  have hTS : T ≤ S := le_Ssub z hzz T hTn
  have hJ : ∀ x ∈ T, x * x = 1 → J x := fun x hx hx2 =>
    c.J_of_mem_prodSub e hn hT₁ hx hx2
  have hconj : ∀ g : G, g⁻¹ * z * g ∉ T := by
    intro g hg
    have h2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hzz]; group
    have hJz := hJ _ hg h2
    exact not_J_z hS θ hn d hQ2 ((J_conj g⁻¹).1 (by rw [inv_inv]; exact hJz))
  obtain ⟨S', hSS'⟩ := hSp.exists_le_sylow
  have hS'le : (S' : Subgroup G) ≤ S := by
    by_contra hnle
    have hne : S ≠ (S' : Subgroup G) := fun heq => hnle (heq ▸ le_rfl)
    have hnil : Group.IsNilpotent (S' : Subgroup G) := S'.isPGroup'.isNilpotent
    have hlt : S.subgroupOf (S' : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne ?_
      refine le_antisymm hSS' fun s hs => ?_
      have : (⟨s, hs⟩ : (S' : Subgroup G)) ∈ S.subgroupOf (S' : Subgroup G) := by
        rw [htop]
        trivial
      exact this
    have hgrow := Group.normalizerCondition_of_isNilpotent (G := (S' : Subgroup G))
      (S.subgroupOf (S' : Subgroup G)) hlt
    obtain ⟨⟨x, hxS'⟩, hxN, hxH⟩ := IsConcreteLE.exists_of_lt hgrow
    have hxS : x ∉ S := fun hx => hxH hx
    have hconjS : ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun s hs =>
      (mem_normalizer_iff.1 hxN ⟨s, hSS' hs⟩).1 hs
    have hz'S : x * z * x⁻¹ ∈ S := hconjS z hzS
    have hz'2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
      calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hz'T : x * z * x⁻¹ ∉ T := by
      intro hmem
      exact not_J_z hS θ hn d hQ2 ((J_conj x).1 (hJ _ hmem hz'2))
    obtain ⟨a, ha, hza⟩ := c.involution_conj hT₁ hz'S hz'T hz'2
    have haT : a ∈ T := ⟨a, ha, 1, one_mem _, by simp [Phi]⟩
    have hy : a⁻¹ * x ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * x * z = a⁻¹ * (x * z * x⁻¹) * x := by group
        _ = a⁻¹ * (a * z * a⁻¹) * x := by rw [hza]
        _ = z * (a⁻¹ * x) := by group
    have hyS' : a⁻¹ * x ∈ (S' : Subgroup G) :=
      S'.mul_mem (S'.inv_mem (hSS' (hTS haT))) hxS'
    obtain ⟨k, hk⟩ := S'.isPGroup' ⟨a⁻¹ * x, hyS'⟩
    have hk' : (a⁻¹ * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨l, hl, hly⟩ := exists_eq_of_two_pow hS θ hn d hQ2 hy (hE hy) hk'
    have hlS' : l ∈ (S' : Subgroup G) := by
      rcases hly with hly | hly
      · rw [← hly]
        exact hyS'
      · have : l = (a⁻¹ * x) * z⁻¹ := by rw [hly]; group
        rw [this]
        exact S'.mul_mem hyS' (S'.inv_mem (hSS' hzS))
    have hX : IsPGroup 2 ((S' : Subgroup G).comap L.subtype) := S'.isPGroup'.comap_subtype
    have hle : (P₀ : Subgroup L) ≤ (S' : Subgroup G).comap L.subtype := by
      intro p hp
      have hp' : (p : G) ∈ P₀' := ⟨p, hp, rfl⟩
      obtain ⟨a', ha', hap⟩ := stageT_exists_diagPre hH c hP₀'L hp'
      have hmemT : Phi z a' a' ∈ T := ⟨a', ha', a', ha', rfl⟩
      show (p : G) ∈ (S' : Subgroup G)
      rw [← hap]
      exact hSS' (hTS hmemT)
    have hmax := P₀.is_maximal' hX hle
    have hlP : (⟨l, hl⟩ : L) ∈ (P₀ : Subgroup L) := by
      rw [← hmax]
      exact hlS'
    have hlP' : l ∈ P₀' := ⟨⟨l, hl⟩, hlP, rfl⟩
    obtain ⟨a', ha', hap⟩ := stageT_exists_diagPre hH c hP₀'L hlP'
    have hlT : l ∈ T := ⟨a', ha', a', ha', hap.symm⟩
    have hyS : a⁻¹ * x ∈ S := by
      rcases hly with hly | hly
      · rw [hly]
        exact hTS hlT
      · rw [hly]
        exact ⟨l, hlT, Or.inr rfl⟩
    have : x = a * (a⁻¹ * x) := by group
    exact hxS (by rw [this]; exact S.mul_mem (hTS haT) hyS)
  have hidx : ¬ 2 ∣ S.index := by
    have := S'.not_dvd_index
    rwa [show (S' : Subgroup G) = S from le_antisymm hS'le hSS'] at this
  have hrel : T.relIndex S = 2 := relIndex_Ssub z hzz T hTn hzT
  have hmin : ∀ y ∈ S, y ∉ T → orderOf z ≤ orderOf y := by
    intro y _ hyT
    have hy1 : y ≠ 1 := fun h1 => hyT (h1 ▸ T.one_mem)
    rw [hz2]
    have h1 := orderOf_pos y
    have h2 : orderOf y ≠ 1 := fun h3 => hy1 (orderOf_eq_one_iff.1 h3)
    omega
  obtain ⟨N, hN, hNidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson (T := S) (U := T)
    hSp hidx hTS hrel hzS hzT hmin hconj
  exact stageT_false_of_index_two hS hNidx

theorem cycTwoWreathFalse_holds : CycTwoWreathFalse := by
  intro G _ _ L Q n θ z h hE M hM
  exact stageT_false h.std θ (by have := h.hn; omega) h.cyc h.card hE hM

end CFSG.OddStandard.AltStdCycTwo
