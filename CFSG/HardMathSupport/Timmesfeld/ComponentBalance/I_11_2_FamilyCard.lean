module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Family

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {G : Type*} [Group G] {ι : Type*} {L : ι → Subgroup G}

section Card

set_option linter.unusedSectionVars false

variable [Fintype ι] [DecidableEq ι] [Finite G]

theorem card_iSup_mul_card_ker (h : CommFam L) :
    Nat.card (⨆ i, L i : Subgroup G) * Nat.card (famProd h).ker = ∏ i, Nat.card (L i) := by
  have := Subgroup.card_ker_mul_card_range (famProd h)
  rw [range_famProd h, Nat.card_pi] at this
  rw [mul_comm]
  exact this

theorem CommFam.centres (h : CommFam L) : CommFam (fun i => centreIn (L i)) :=
  fun _ _ hij x y hx hy => h hij x y (centreIn_le _ hx) (centreIn_le _ hy)

@[expose] def centreInclusion (L : ι → Subgroup G) : (∀ i, centreIn (L i)) →* ∀ i, L i :=
  MonoidHom.pi fun i => (Subgroup.inclusion (centreIn_le (L i))).comp (Pi.evalMonoidHom _ i)

theorem centreInclusion_injective : Function.Injective (centreInclusion L) := by
  intro f g hfg
  funext i
  have := congrFun hfg i
  have h2 : ((f i : centreIn (L i)) : G) = (g i : G) := congrArg (fun x : L i => (x : G)) this
  exact Subtype.ext h2

theorem famProd_centreInclusion (h : CommFam L) (f : ∀ i, centreIn (L i)) :
    famProd h (centreInclusion L f) = famProd h.centres f := by
  rw [famProd_apply, famProd_apply]
  rfl

theorem map_centreInclusion_ker (h : CommFam L) :
    (famProd h.centres).ker.map (centreInclusion L) = (famProd h).ker := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have h1 : famProd h.centres f = 1 := hf
    show famProd h (centreInclusion L f) = 1
    rw [famProd_centreInclusion, h1]
  · intro hg
    refine ⟨fun k => ⟨(g k : G), ker_famProd_apply_mem_centreIn h hg k⟩, ?_, ?_⟩
    · have h1 : famProd h g = 1 := hg
      show famProd h.centres _ = 1
      rw [← famProd_centreInclusion, ← h1]
      rfl
    · funext k
      rfl

theorem card_ker_centre_eq (h : CommFam L) :
    Nat.card (famProd h.centres).ker = Nat.card (famProd h).ker := by
  rw [← map_centreInclusion_ker h]
  exact (Subgroup.card_map_of_injective centreInclusion_injective).symm

theorem card_centreIn_iSup_mul_card_ker (h : CommFam L) :
    Nat.card (centreIn (⨆ i, L i)) * Nat.card (famProd h).ker =
      ∏ i, Nat.card (centreIn (L i)) := by
  have := Subgroup.card_ker_mul_card_range (famProd h.centres)
  rw [range_famProd h.centres, ← h.centreIn_iSup_eq_iSup, Nat.card_pi,
    card_ker_centre_eq h] at this
  rw [mul_comm]
  exact this

theorem CommFam.card_centreIn_iSup_le_prod (h : CommFam L) :
    Nat.card (centreIn (⨆ i, L i)) ≤ ∏ i, Nat.card (centreIn (L i)) := by
  rw [← card_centreIn_iSup_mul_card_ker h]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem CommFam.card_iSup_le_prod (h : CommFam L) :
    Nat.card (⨆ i, L i : Subgroup G) ≤ ∏ i, Nat.card (L i) := by
  rw [← card_iSup_mul_card_ker h]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem CommFam.iSupIndep_iff_ker_eq_bot (h : CommFam L) :
    iSupIndep L ↔ (famProd h).ker = ⊥ := by
  constructor
  · intro hind
    rw [eq_bot_iff]
    intro f hf
    have hinj : Function.Injective (famProd h) :=
      Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
    have : f = 1 := hinj (by rw [(MonoidHom.mem_ker.1 hf), map_one])
    simp [this]
  · intro hker
    have hinj : Function.Injective (famProd h) := (MonoidHom.ker_eq_bot_iff _).1 hker
    rw [iSupIndep_def]
    intro k
    rw [Subgroup.disjoint_def]
    intro x hxk hxr
    let T : Subgroup (∀ i, L i) := Subgroup.pi ({k} : Set ι) fun _ => ⊥
    have hle : restSup L k ≤ T.map (famProd h) := by
      refine iSup₂_le fun j hj => ?_
      intro y hy
      refine Subgroup.mem_map.2 ⟨Pi.mulSingle j ⟨y, hy⟩, ?_, famProd_mulSingle h j ⟨y, hy⟩⟩
      rw [Subgroup.mem_pi]
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      rw [Pi.mulSingle_eq_of_ne hj.symm]
      exact Subgroup.one_mem _
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 (hle hxr)
    have hgk : g k = 1 := by
      have := (Subgroup.mem_pi _).1 hg k (Set.mem_singleton k)
      exact Subgroup.mem_bot.1 this
    have : g = Pi.mulSingle k ⟨x, hxk⟩ := hinj (by rw [hgx, famProd_mulSingle])
    have h2 := congrFun this k
    rw [hgk, Pi.mulSingle_eq_same] at h2
    exact congrArg Subtype.val h2.symm

theorem CommFam.card_centreIn_iSup_eq_prod_iff (h : CommFam L) :
    Nat.card (centreIn (⨆ i, L i)) = ∏ i, Nat.card (centreIn (L i)) ↔ iSupIndep L := by
  rw [h.iSupIndep_iff_ker_eq_bot]
  have key := card_centreIn_iSup_mul_card_ker h
  have hpos : 0 < Nat.card (centreIn (⨆ i, L i)) := Nat.card_pos
  constructor
  · intro hc
    rw [hc] at key
    have hprod : 0 < ∏ i, Nat.card (centreIn (L i)) := hc ▸ hpos
    have : Nat.card (famProd h).ker = 1 := by
      have := Nat.eq_of_mul_eq_mul_left hprod (key.trans (mul_one _).symm)
      exact this
    exact Subgroup.card_eq_one.1 this
  · intro hker
    rw [hker, Subgroup.card_bot, mul_one] at key
    exact key

theorem CommFam.inf_restSup_eq_bot_of_card_centreIn (h : CommFam L)
    (hc : Nat.card (centreIn (⨆ i, L i)) = ∏ i, Nat.card (centreIn (L i))) (k : ι) :
    L k ⊓ restSup L k = ⊥ :=
  disjoint_iff.1 ((iSupIndep_def.1 ((h.card_centreIn_iSup_eq_prod_iff).1 hc)) k)

theorem CommFam.card_iSup_eq_prod (h : CommFam L) (hind : iSupIndep L) :
    Nat.card (⨆ i, L i : Subgroup G) = ∏ i, Nat.card (L i) := by
  have key := card_iSup_mul_card_ker h
  rw [(h.iSupIndep_iff_ker_eq_bot).1 hind, Subgroup.card_bot, mul_one] at key
  exact key

theorem CommFam.card_iSup_eq_prod_of_card_centreIn (h : CommFam L)
    (hc : Nat.card (centreIn (⨆ i, L i)) = ∏ i, Nat.card (centreIn (L i))) :
    Nat.card (⨆ i, L i : Subgroup G) = ∏ i, Nat.card (L i) :=
  h.card_iSup_eq_prod ((h.card_centreIn_iSup_eq_prod_iff).1 hc)

theorem CommFam.card_iSup_eq_prod_of_le (h : CommFam L) (hind : iSupIndep L)
    (E : ι → Subgroup G) (hE : ∀ i, E i ≤ L i) :
    Nat.card (⨆ i, E i : Subgroup G) = ∏ i, Nat.card (E i) :=
  (show CommFam E from fun _ _ hij x y hx hy => h hij x y (hE _ hx) (hE _ hy)).card_iSup_eq_prod
    (hind.mono hE)

end Card

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

end
