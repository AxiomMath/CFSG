module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Fields
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XCheck

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

section Perm

theorem wP_append (a b : List ℕ) : wP (a ++ b) = wP a * wP b := by
  simp [wP, List.map_append, List.prod_append]

theorem wP_cons (k : ℕ) (w : List ℕ) : wP (k :: w) = gP k * wP w := by
  simp [wP]

theorem xId_spec : ∀ p ∈ xIds, wP p.1 = wP p.2 := by
  intro p hp
  have hval : (∀ k ∈ p.1, k < 18) ∧ ∀ k ∈ p.2, k < 18 := by
    revert p
    decide
  have h := List.all_eq_true.1 xId_check p hp
  exact eq_of_eqA (rep_wA tabs_check _ hval.1) (rep_wA tabs_check _ hval.2) h

theorem xId_at (i : ℕ) (hi : i < xIds.length) : wP xIds[i].1 = wP xIds[i].2 :=
  xId_spec _ (List.getElem_mem hi)

theorem xId_of_mem {a b : List ℕ} (h : (a, b) ∈ xIds) : wP a = wP b := xId_spec _ h

theorem prodCheck_spec {f : List ℕ → List ℕ → List ℕ} {data : List (ℕ × List (List ℕ × List ℕ))}
    (h : prodCheck f data = true) (hlt : ∀ p ∈ data, p.1 < 18 ∧ ∀ k ∈ prodWord f p.2, k < 18) :
    ∀ p ∈ data, wP [p.1] = wP (prodWord f p.2) := by
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  exact eq_of_eqA (rep_wA tabs_check _ (by simpa using (hlt p hp).1))
    (rep_wA tabs_check _ (hlt p hp).2) h1

theorem gP_mul_self {k : ℕ} (hk : k < 18) : gP k * gP k = 1 := by
  have hlen : k < xIds.length := lt_of_lt_of_le hk (by decide)
  have h := xId_at k hlen
  have e1 : xIds[k] = ([k, k], []) := by
    interval_cases k <;> rfl
  rw [e1] at h
  simpa [wP] using h

theorem gP_inv {k : ℕ} (hk : k < 18) : (gP k)⁻¹ = gP k :=
  inv_eq_of_mul_eq_one_right (gP_mul_self hk)

theorem wP_reverse : ∀ w : List ℕ, (∀ k ∈ w, k < 18) → wP w.reverse = (wP w)⁻¹
  | [], _ => by simp [wP]
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 18 := fun j hj => hw j (List.mem_cons_of_mem k hj)
    rw [List.reverse_cons, wP_append, wP_reverse w hw', wP_cons k w, mul_inv_rev, wP_single,
      gP_inv hk]

end Perm

theorem wP_mem_of_letters {c : ChainData} :
    ∀ w : List ℕ, (∀ k ∈ w, [k] ∈ c.gens) → wP w ∈ c.grp
  | [], _ => by simp [wP]
  | k :: w, hw => by
    rw [wP_cons]
    refine mul_mem ?_ (wP_mem_of_letters w fun j hj => hw j (List.mem_cons_of_mem k hj))
    rw [← wP_single]
    exact wP_mem_grp (hw k List.mem_cons_self)

theorem grp_le_of_subset {c c' : ChainData}
    (h : ∀ w ∈ c.gens, w ∈ c'.gens) : c.grp ≤ c'.grp :=
  grp_le fun w hw => wP_mem_grp (h w hw)

theorem commCheck_spec {as bs : List (List ℕ)}
    (h : commCheck as bs = true) (ha : ∀ a ∈ as, ∀ k ∈ a, k < 18)
    (hb : ∀ b ∈ bs, ∀ k ∈ b, k < 18) : ∀ a ∈ as, ∀ b ∈ bs, wP a * wP b = wP b * wP a := by
  intro a hamem b hbmem
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h a hamem) b hbmem
  have hab : ∀ k ∈ a ++ b, k < 18 := fun k hk =>
    (List.mem_append.1 hk).elim (ha a hamem k) (hb b hbmem k)
  have hba : ∀ k ∈ b ++ a, k < 18 := fun k hk =>
    (List.mem_append.1 hk).elim (hb b hbmem k) (ha a hamem k)
  have := eq_of_eqA (rep_wA tabs_check _ hab) (rep_wA tabs_check _ hba) h1
  rwa [wP_append, wP_append] at this

theorem grp_le_centralizer {c c' : ChainData}
    (h : ∀ a ∈ c.gens, ∀ b ∈ c'.gens, wP a * wP b = wP b * wP a) :
    c.grp ≤ centralizer (c'.grp : Set (Equiv.Perm (Fin 693))) := by
  refine closure_le_centralizer ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact h a ha b hb

section GLevel

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

variable (e) in
@[expose] noncomputable def gw (w : List ℕ) : G := phiG e (yamWord w)

theorem gw_eq (w : List ℕ) (hw : ∀ k ∈ w, k < 18) : gw e w = iotaG e (tw w hw) := by
  rw [gw, phiG_apply, psiT_yamWord w hw]

theorem gw_append (a b : List ℕ) : gw e (a ++ b) = gw e a * gw e b := by
  simp only [gw, yamWord, List.map_append, List.prod_append, map_mul]

theorem gw_nil : gw e [] = 1 := by simp [gw, yamWord]

theorem gw_mem_L (w : List ℕ) : gw e w ∈ L := phiG_mem _

theorem gw_mem_toG {H : Subgroup (Equiv.Perm (Fin 693))} {w : List ℕ} (hw : ∀ k ∈ w, k < 18) :
    gw e w ∈ toG e H ↔ wP w ∈ H := by
  rw [gw_eq w hw, iotaG_mem_toG]
  rfl

theorem gw_eq_gw {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18)
    (h : wP a = wP b) : gw e a = gw e b := by
  rw [gw_eq a ha, gw_eq b hb]
  exact congrArg (iotaG e) (Subtype.ext h)

theorem toG_le_of_gens {c : ChainData} (hc : c.GensOK) {X : Subgroup G}
    (h : ∀ w ∈ c.gens, gw e w ∈ X) : toG e c.grp ≤ X := by
  suffices H : ∀ g ∈ c.grp, ∀ hT : g ∈ T46, iotaG e ⟨g, hT⟩ ∈ X by
    intro x hx
    obtain ⟨⟨g, hT⟩, hg, rfl⟩ := mem_toG.1 hx
    exact H g hg hT
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro hT
    have := h w hw
    rwa [gw_eq w (hc w hw)] at this
  | one =>
    intro hT
    have e1 : (⟨1, hT⟩ : T46) = 1 := rfl
    rw [e1, map_one]
    exact one_mem X
  | mul x y hx hy ihx ihy =>
    intro hT
    have e1 : (⟨x * y, hT⟩ : T46) = ⟨x, grp_le_T46 hc hx⟩ * ⟨y, grp_le_T46 hc hy⟩ := rfl
    rw [e1, map_mul]
    exact mul_mem (ihx _) (ihy _)
  | inv x hx ihx =>
    intro hT
    have e1 : (⟨x⁻¹, hT⟩ : T46) = (⟨x, grp_le_T46 hc hx⟩ : T46)⁻¹ := rfl
    rw [e1, map_inv]
    exact inv_mem (ihx _)

theorem toG_le_normalizer {H K : Subgroup (Equiv.Perm (Fin 693))} (hH : H ≤ T46) (hK : K ≤ T46)
    (h : H ≤ normalizer (K : Set (Equiv.Perm (Fin 693)))) :
    toG e H ≤ normalizer (toG e K : Set G) := fun x hx => by
  have h1 : x ∈ toG e (normalizer (K : Set (Equiv.Perm (Fin 693))) ⊓ T46) :=
    toG_mono (le_inf h hH) hx
  rw [← normalizer_toG hK] at h1
  exact h1.1

theorem toG_le_centralizer {H K : Subgroup (Equiv.Perm (Fin 693))}
    (h : H ≤ centralizer (K : Set (Equiv.Perm (Fin 693)))) :
    toG e H ≤ centralizer (toG e K : Set G) := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 hx
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, hk, rfl⟩ := mem_toG.1 hy
  rw [← map_mul, ← map_mul]
  exact congrArg (iotaG e) (Subtype.ext (mem_centralizer_iff.1 (h hg) k hk))

theorem toG_inf_centralizer_le {H K M : Subgroup (Equiv.Perm (Fin 693))} (hK : K ≤ T46)
    (h : ∀ g ∈ H, g ∈ T46 → (∀ k ∈ K, g * k = k * g) → g ∈ M) :
    toG e H ⊓ centralizer (toG e K : Set G) ≤ toG e M := by
  rintro x ⟨hx, hc⟩
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 hx
  refine mem_toG.2 ⟨g, h g hg g.2 fun k hk => ?_, rfl⟩
  have := mem_centralizer_iff.1 hc (iotaG e ⟨k, hK hk⟩) (iotaG_mem_toG.2 hk)
  rw [← map_mul, ← map_mul] at this
  exact (congrArg Subtype.val (iotaG_injective this)).symm

theorem toG_inf_centralizer_gw_le {H M : Subgroup (Equiv.Perm (Fin 693))} {w : List ℕ}
    (hw : ∀ k ∈ w, k < 18) (h : ∀ g ∈ H, g ∈ T46 → g * wP w = wP w * g → g ∈ M) :
    toG e H ⊓ centralizer ({gw e w} : Set G) ≤ toG e M := by
  rintro x ⟨hx, hc⟩
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 hx
  refine mem_toG.2 ⟨g, h g hg g.2 ?_, rfl⟩
  have := mem_centralizer_iff.1 hc (gw e w) rfl
  rw [gw_eq w hw, ← map_mul, ← map_mul] at this
  exact (congrArg Subtype.val (iotaG_injective this)).symm

theorem toG_chZ : toG e chZ.grp = zpowers (gw e [14]) := by
  have h1 : chZ.grp = zpowers ((tw [14] (by decide) : T46) : Equiv.Perm (Fin 693)) := by
    rw [ChainData.grp, Subgroup.zpowers_eq_closure]
    congr 1
    ext x
    simp [chZ, tw]
  rw [h1, toG_zpowers, gw_eq [14] (by decide)]

theorem gw_reverse {w : List ℕ} (hw : ∀ k ∈ w, k < 18) : gw e w.reverse = (gw e w)⁻¹ := by
  rw [gw_eq w hw, gw_eq w.reverse (fun k hk => hw k (List.mem_reverse.1 hk)), ← map_inv]
  exact congrArg (iotaG e) (Subtype.ext (wP_reverse w hw))

theorem gw_conj {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) :
    gw e (a ++ b ++ a.reverse) = gw e a * gw e b * (gw e a)⁻¹ := by
  rw [gw_append, gw_append, gw_reverse ha]

theorem gw_comm {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) :
    gw e (a ++ b ++ a.reverse ++ b.reverse) = ⁅gw e a, gw e b⁆ := by
  rw [gw_append, gw_append, gw_append, gw_reverse ha, gw_reverse hb, commutatorElement_def]

end GLevel

section Witness

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46}

theorem gw_prodWord_mem {f : List ℕ → List ℕ → List ℕ} {X : Subgroup G} :
    ∀ bs : List (List ℕ × List ℕ), (∀ b ∈ bs, gw e (f b.1 b.2) ∈ X) → gw e (prodWord f bs) ∈ X
  | [], _ => by simp [prodWord, gw_nil, one_mem]
  | b :: bs, h => by
    have e1 : prodWord f (b :: bs) = f b.1 b.2 ++ prodWord f bs := by simp [prodWord]
    rw [e1, gw_append]
    exact mul_mem (h b List.mem_cons_self)
      (gw_prodWord_mem bs fun b' hb' => h b' (List.mem_cons_of_mem b hb'))

theorem toG_le_of_prodCheck {c : ChainData} (hc : c.GensOK) {f : List ℕ → List ℕ → List ℕ}
    {data : List (ℕ × List (List ℕ × List ℕ))} (hcheck : prodCheck f data = true)
    (hlt : ∀ p ∈ data, p.1 < 18 ∧ ∀ k ∈ prodWord f p.2, k < 18)
    (hcov : ∀ w ∈ c.gens, ∃ p ∈ data, w = [p.1]) {X : Subgroup G}
    (hX : ∀ p ∈ data, ∀ b ∈ p.2, gw e (f b.1 b.2) ∈ X) : toG e c.grp ≤ X := by
  refine toG_le_of_gens hc fun w hw => ?_
  obtain ⟨p, hp, rfl⟩ := hcov w hw
  rw [gw_eq_gw (by simpa using (hlt p hp).1) (hlt p hp).2 (prodCheck_spec hcheck hlt p hp)]
  exact gw_prodWord_mem p.2 (hX p hp)

theorem gw_cwW {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) :
    gw e (cwW a b) = ⁅gw e a, gw e b⁆ := gw_comm ha hb

theorem gw_cjW {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) :
    gw e (cjW a b) = gw e a * gw e b * (gw e a)⁻¹ := gw_conj ha

end Witness

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
