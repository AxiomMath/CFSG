module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Strong
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Excl
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N

section Transport

variable {Γ : Type*} [Group Γ] {Hs : Subgroup Γ}

theorem exists_sylow_coe_eq_subgroupOf {p : ℕ} {Sb : Subgroup Γ} (h : fusionIsSylowIn p Sb Hs) :
    ∃ P : Sylow p ↥Hs, (P : Subgroup ↥Hs) = Sb.subgroupOf Hs := by
  obtain ⟨hSH, hS, hmax⟩ := h
  refine ⟨⟨Sb.subgroupOf Hs, hS.comap_subtype, fun {Q} hQ hSQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map Hs.subtype) (Subgroup.map_subtype_le Q) (hQ.map Hs.subtype)
    fun s hs => ⟨⟨s, hSH hs⟩, hSQ (show (⟨s, hSH hs⟩ : ↥Hs) ∈ Sb.subgroupOf Hs from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective Hs.subtype_injective Q).symm

theorem map_subtype_conj_eq_conj_map_subtype (g : ↥Hs) (B : Subgroup ↥Hs) :
    (B.map (MulAut.conj g).toMonoidHom).map Hs.subtype =
      (B.map Hs.subtype).map (MulAut.conj (g : Γ)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_subtype_commutator_zpowers (B : Subgroup ↥Hs) (j : ↥Hs) :
    (⁅B, zpowers j⁆ : Subgroup ↥Hs).map Hs.subtype = ⁅B.map Hs.subtype, zpowers (j : Γ)⁆ := by
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.coe_subtype]

theorem card_commutator_zpowers_subgroupOf {W : Subgroup Γ} (hWHs : W ≤ Hs) (j : ↥Hs) :
    Nat.card (⁅W.subgroupOf Hs, zpowers j⁆ : Subgroup ↥Hs) =
      Nat.card (⁅W, zpowers (j : Γ)⁆ : Subgroup Γ) := by
  have h := map_subtype_commutator_zpowers (W.subgroupOf Hs) j
  rw [Subgroup.map_subgroupOf_eq_of_le hWHs] at h
  rw [← h, Subgroup.card_map_of_injective Hs.subtype_injective]

theorem mem_normalizer_subgroupOf_iff_coe_mem {W : Subgroup Γ} (hWHs : W ≤ Hs) (g : ↥Hs) :
    g ∈ normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) ↔
      (g : Γ) ∈ normalizer (W : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h n
    by_cases hn : n ∈ Hs
    · exact h ⟨n, hn⟩
    · have hgn : (g : Γ) * n * (g : Γ)⁻¹ ∉ Hs := fun hc => hn (by
        have e : n = (g : Γ)⁻¹ * ((g : Γ) * n * (g : Γ)⁻¹) * g := by group
        rw [e]
        exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem g.2) hc) g.2)
      exact iff_of_false (fun hc => hn (hWHs hc)) (fun hc => hgn (hWHs hc))
  · intro h n
    exact h n

theorem mem_centralizer_subgroupOf_iff_coe_mem {W : Subgroup Γ} (hWHs : W ≤ Hs) (g : ↥Hs) :
    g ∈ centralizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) ↔
      (g : Γ) ∈ centralizer (W : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    exact congrArg Subtype.val (h ⟨w, hWHs hw⟩ hw)
  · intro h w hw
    exact Subtype.ext (h (w : Γ) hw)

theorem map_subtype_normalizer_subgroupOf_eq_inf {W : Subgroup Γ} (hWHs : W ≤ Hs) :
    (normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs)).map Hs.subtype =
      normalizer (W : Set Γ) ⊓ Hs := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_normalizer_subgroupOf_iff_coe_mem hWHs g).1 hg, g.2⟩
  · rintro ⟨hy, hyHs⟩
    exact ⟨⟨y, hyHs⟩, (mem_normalizer_subgroupOf_iff_coe_mem hWHs ⟨y, hyHs⟩).2 hy, rfl⟩

theorem map_subtype_centralizer_subgroupOf_eq_inf {W : Subgroup Γ} (hWHs : W ≤ Hs) :
    (centralizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs)).map Hs.subtype =
      centralizer (W : Set Γ) ⊓ Hs := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_centralizer_subgroupOf_iff_coe_mem hWHs g).1 hg, g.2⟩
  · rintro ⟨hy, hyHs⟩
    exact ⟨⟨y, hyHs⟩, (mem_centralizer_subgroupOf_iff_coe_mem hWHs ⟨y, hyHs⟩).2 hy, rfl⟩

theorem card_imgIn_subgroupOf [Finite Γ] {W : Subgroup Γ} (hWHs : W ≤ Hs) :
    Nat.card (imgIn (W.subgroupOf Hs) (normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs))) =
      Nat.card (imgIn W (normalizer (W : Set Γ) ⊓ Hs)) := by
  have h1 := card_imgIn_mul_card (W.subgroupOf Hs)
    (normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs))
  have h2 := card_imgIn_mul_card W (normalizer (W : Set Γ) ⊓ Hs)
  have hN : Nat.card (normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) ⊓
      normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) : Subgroup ↥Hs) =
      Nat.card (normalizer (W : Set Γ) ⊓ Hs ⊓ normalizer (W : Set Γ) : Subgroup Γ) := by
    rw [inf_idem, inf_right_comm, inf_idem, ← map_subtype_normalizer_subgroupOf_eq_inf hWHs,
      Subgroup.card_map_of_injective Hs.subtype_injective]
  have hlat : normalizer (W : Set Γ) ⊓ Hs ⊓ (centralizer (W : Set Γ) ⊓ Hs) =
      normalizer (W : Set Γ) ⊓ Hs ⊓ centralizer (W : Set Γ) :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_right)))
  have hC : Nat.card (normalizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) ⊓
      centralizer ((W.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) : Subgroup ↥Hs) =
      Nat.card (normalizer (W : Set Γ) ⊓ Hs ⊓ centralizer (W : Set Γ) : Subgroup Γ) := by
    rw [← Subgroup.card_map_of_injective Hs.subtype_injective,
      Subgroup.map_inf_eq _ _ _ Hs.subtype_injective, map_subtype_normalizer_subgroupOf_eq_inf hWHs,
      map_subtype_centralizer_subgroupOf_eq_inf hWHs, hlat]
  have hpos : 0 < Nat.card (normalizer (W : Set Γ) ⊓ Hs ⊓ centralizer (W : Set Γ) : Subgroup Γ) :=
    Nat.card_pos
  rw [hC, hN] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem isSolvable_centralizer_of_subtype (t : ↥Hs)
    (h : Group.IsSolvable ↥(centralizer ({(t : Γ)} : Set Γ) ⊓ Hs)) :
    Group.IsSolvable ↥(centralizer ({t} : Set ↥Hs)) := by
  let φ : ↥(centralizer ({t} : Set ↥Hs)) →* ↥(centralizer ({(t : Γ)} : Set Γ) ⊓ Hs) :=
    (Hs.subtype.comp (centralizer ({t} : Set ↥Hs)).subtype).codRestrict _ fun c => by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 ?_, (c : ↥Hs).2⟩
      rintro _ rfl
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 c.2 t rfl)
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun a b hab => ?_
  have h1 : ((φ a : ↥(centralizer ({(t : Γ)} : Set Γ) ⊓ Hs)) : Γ) = (φ b : Γ) :=
    congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h1)

theorem stronglyClosed_subgroupOf_of_rank [Finite Γ] {W Sb : Subgroup Γ} (T : Sylow 2 ↥Hs)
    (hT : (T : Subgroup ↥Hs) = Sb.subgroupOf Hs) (hWHs : W ≤ Hs) (hWab : IsElemAbelian 2 W)
    (hWS : W ≤ Sb)
    (hweak : ∀ g : Γ, g ∈ Hs → W.map (MulAut.conj g).toMonoidHom ≤ Sb →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hP0 : ∀ B : Subgroup Γ, B ≤ Sb → IsElemAbelian 2 B → W.relIndex B ≤ 8)
    (hP1 : ∀ j ∈ Sb, j ∉ W → j * j = 1 → 4 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ))
    (hP2 : ∀ F : Subgroup Γ, F ≤ Sb → W ≤ F → W.relIndex F = 4 → (∀ p ∈ F, p * p ∈ W) →
      ∃ j ∈ F, j ∉ W ∧ 16 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ)) :
    ∀ a ∈ W.subgroupOf Hs, ∀ g : ↥Hs, g⁻¹ * a * g ∈ (T : Subgroup ↥Hs) →
      g⁻¹ * a * g ∈ W.subgroupOf Hs := by
  have hmapW : (W.subgroupOf Hs).map Hs.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWHs
  have hmapT : ∀ {B : Subgroup ↥Hs}, B ≤ T → B.map Hs.subtype ≤ Sb := by
    intro B hB
    rw [hT] at hB
    exact Subgroup.map_le_iff_le_comap.2 hB
  have hWT : W.subgroupOf Hs ≤ (T : Subgroup ↥Hs) := by
    rw [hT]
    exact fun a ha => hWS ha
  refine Strong.stronglyClosed_of_rank T (hWab.subgroupOf Hs) hWT ?_ ?_ ?_ ?_
  · intro g hg
    have key : ((W.subgroupOf Hs).map (MulAut.conj g).toMonoidHom).map Hs.subtype =
        W.map (MulAut.conj (g : Γ)).toMonoidHom := by
      rw [map_subtype_conj_eq_conj_map_subtype, hmapW]
    apply Subgroup.map_injective Hs.subtype_injective
    rw [key, hmapW]
    exact hweak g g.2 (by rw [← key]; exact hmapT hg)
  · intro B hB hBab
    exact (Subgroup.relIndex_comap W Hs.subtype B).trans_le (hP0 _ (hmapT hB) (hBab.map Hs.subtype))
  · intro j hj hjW hj2
    rw [card_commutator_zpowers_subgroupOf hWHs]
    refine hP1 (j : Γ) ?_ hjW ?_
    · rw [hT] at hj
      exact hj
    · exact congrArg Subtype.val hj2
  · intro F hFT hWF hrel hsq
    obtain ⟨j, ⟨j', hj'F, rfl⟩, hjW, hj16⟩ := hP2 (F.map Hs.subtype) (hmapT hFT)
      (hmapW.symm.le.trans (Subgroup.map_mono hWF))
      ((Subgroup.relIndex_comap W Hs.subtype F).symm.trans hrel)
      (by rintro _ ⟨f, hf, rfl⟩; exact hsq f hf)
    refine ⟨j', hj'F, hjW, ?_⟩
    rw [card_commutator_zpowers_subgroupOf hWHs]
    exact hj16

end Transport

section


theorem six25 (hTop : TopStatement) {Γ : Type} [Group Γ] [Finite Γ]
    {Hs W Sb U : Subgroup Γ} {x t s : Γ}
    (hSyl : fusionIsSylowIn 2 Sb Hs) (hWHs : W ≤ Hs) (hWab : IsElemAbelian 2 W)
    (hW : Nat.card W = 256) (hWS : W ≤ Sb)
    (hweak : ∀ g : Γ, g ∈ Hs → W.map (MulAut.conj g).toMonoidHom ≤ Sb →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hP0 : ∀ B : Subgroup Γ, B ≤ Sb → IsElemAbelian 2 B → W.relIndex B ≤ 8)
    (hP1 : ∀ j ∈ Sb, j ∉ W → j * j = 1 → 4 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ))
    (hP2 : ∀ F : Subgroup Γ, F ≤ Sb → W ≤ F → W.relIndex F = 4 → (∀ p ∈ F, p * p ∈ W) →
      ∃ j ∈ F, j ∉ W ∧ 16 ≤ Nat.card (⁅W, zpowers j⁆ : Subgroup Γ))
    (hxHs : x ∈ Hs) (htHs : t ∈ Hs) (hsHs : s ∈ Hs)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (ht2 : t * t = 1) (htx : t * x = x * t)
    (hxW : x ∈ normalizer (W : Set Γ)) (htW : t ∈ normalizer (W : Set Γ))
    (hfpf : ∀ a ∈ W, x * a * x⁻¹ = a → a = 1)
    (hUW : U ≤ W) (hU : Nat.card U = 16) (hCt : ∀ a ∈ W, t * a * t⁻¹ = a ↔ a ∈ U)
    (hs : ∃ h ∈ Hs, s = h * t * h⁻¹) (hsW : s ∈ normalizer (W : Set Γ))
    (hv : (t * s) * x * (t * s)⁻¹ = x⁻¹)
    (hsolv : Group.IsSolvable ↥(centralizer ({t} : Set Γ) ⊓ Hs))
    (hIα : Nat.card (imgIn W (normalizer (W : Set Γ) ⊓ Hs)) ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2) :
    ∀ h ∈ Hs, ∀ y ∈ W ⊔ (goldschmidtOddCore ↥Hs).map Hs.subtype,
      h * y * h⁻¹ ∈ W ⊔ (goldschmidtOddCore ↥Hs).map Hs.subtype := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq_subgroupOf hSyl
  have hAS : W.subgroupOf Hs ≤ (S : Subgroup ↥Hs) := by
    rw [hS]
    exact fun a ha => hWS ha
  have hab : IsElemAbelian 2 (W.subgroupOf Hs) := hWab.subgroupOf Hs
  have hA : Nat.card (W.subgroupOf Hs) = 256 := by
    rw [← hW]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWHs).toEquiv
  have hcl := stronglyClosed_subgroupOf_of_rank S hS hWHs hWab hWS hweak hP0 hP1 hP2
  have hfpf' : ∀ a ∈ W.subgroupOf Hs,
      (⟨x, hxHs⟩ : ↥Hs) * a * (⟨x, hxHs⟩ : ↥Hs)⁻¹ = a → a = 1 := by
    intro a ha h
    exact Subtype.ext (hfpf (a : Γ) ha (congrArg Subtype.val h))
  have hCt' : ∀ a ∈ W.subgroupOf Hs,
      (⟨t, htHs⟩ : ↥Hs) * a * (⟨t, htHs⟩ : ↥Hs)⁻¹ = a ↔ a ∈ U.subgroupOf Hs := by
    intro a ha
    exact Subtype.ext_iff.trans (hCt (a : Γ) ha)
  have hs' : ∃ h : ↥Hs, (⟨s, hsHs⟩ : ↥Hs) = h * ⟨t, htHs⟩ * h⁻¹ := by
    obtain ⟨h, hh, rfl⟩ := hs
    exact ⟨⟨h, hh⟩, Subtype.ext rfl⟩
  have hbot := Gold.layer_eq_bot hTop S hAS hab hA hcl (x := ⟨x, hxHs⟩) (t := ⟨t, htHs⟩)
    (Subtype.ext hx5) (fun h => hx1 (congrArg Subtype.val h))
    (Subtype.ext ht2) (Subtype.ext htx)
    ((mem_normalizer_subgroupOf_iff_coe_mem hWHs _).2 hxW)
    ((mem_normalizer_subgroupOf_iff_coe_mem hWHs _).2 htW) hfpf' (U := U.subgroupOf Hs)
    (fun a ha => hUW ha)
    (by
      rw [← hU]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hUW.trans hWHs)).toEquiv)
    hCt' (s := ⟨s, hsHs⟩) hs' ((mem_normalizer_subgroupOf_iff_coe_mem hWHs _).2 hsW)
    (Subtype.ext hv) (isSolvable_centralizer_of_subtype ⟨t, htHs⟩ hsolv)
    (by rw [card_imgIn_subgroupOf hWHs]; exact hIα)
  have hN := (Gold.normal_of_layer_bot hTop S hAS hab.1 hcl hbot).2.2
  have hmap : (W.subgroupOf Hs ⊔ goldschmidtOddCore ↥Hs).map Hs.subtype =
      W ⊔ (goldschmidtOddCore ↥Hs).map Hs.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hWHs]
  intro h hh y hy
  rw [← hmap] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨h, hh⟩ * y' * ⟨h, hh⟩⁻¹, hN.conj_mem y' hy' ⟨h, hh⟩, rfl⟩

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
