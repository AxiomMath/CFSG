module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoAct
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModIsoMap

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup Matrix ModT10
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace ModIso

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem mulVec_conj (P g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((P * g * P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        ((P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) =
      (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

theorem mulVec_inv_mulVec' (P : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem exists_psi (c : Config G L Q n θ z) {T S₀ D : Subgroup G} (g1 : G1Data c T S₀ D) :
    ∃ Ψ : T10 →* G, Function.Injective Ψ ∧ Qm.map Ψ = T ∧ Ψ tm = z ∧ Mm.map Ψ = MB T D ∧
      Ψ.range = TB T S₀ := by
  obtain ⟨cT, hcT⟩ := exists_tCoords c g1.hH
  obtain ⟨hzS₀, hS₀le, P, δ, hδ⟩ := s0_struct c g1
  set Pm : Matrix (Fin 3) (Fin 3) (ZMod 2) := (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hPm
  let c' : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G := fun v w => cT (Pm *ᵥ v) (Pm *ᵥ w)
  let δG : sylowT →* G := D.subtype.comp δ.toMonoidHom
  have hδG : ∀ g, δG g = ((δ g : D) : G) := fun _ => rfl
  have hPinj : ∀ v, Pm *ᵥ v = 0 → v = 0 := fun v h => by
    have h1 := congrArg (((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ·) h
    simp only [hPm, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at h1
    exact h1
  have hdata : MapData T z c' δG :=
    { mem := fun v w => hcT.mem _ _
      add := fun v w v' w' => by
        show cT (Pm *ᵥ (v + v')) (Pm *ᵥ (w + w')) =
          cT (Pm *ᵥ v) (Pm *ᵥ w) * cT (Pm *ᵥ v') (Pm *ᵥ w')
        rw [mulVec_add, mulVec_add, hcT.add]
      surj := fun t ht => by
        obtain ⟨v, w, rfl⟩ := hcT.surj t ht
        refine ⟨((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v,
          ((P⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w, ?_⟩
        show cT (Pm *ᵥ _) (Pm *ᵥ _) = cT v w
        rw [hPm, mulVec_inv_mulVec', mulVec_inv_mulVec']
      inj := fun v w h => by
        obtain ⟨hv, hw⟩ := hcT.inj _ _ h
        exact ⟨hPinj v hv, hPinj w hw⟩
      conj_z := fun v w => by
        show z * cT (Pm *ᵥ v) (Pm *ᵥ w) * z⁻¹ = cT (Pm *ᵥ (v + w)) (Pm *ᵥ w)
        rw [hcT.conj_z, mulVec_add]
      conj_δ := fun g v w => by
        obtain ⟨b, hb⟩ := hδ g
        have hnorm : ((δ g : D) : G) ∈ normalizer (T : Set G) := g1.S₀_norm (g1.D_le_S₀ (δ g).2)
        have h1 := hcT.conj_lin (P * g * P⁻¹) _ hnorm ⟨_, N0.eps_mem_E θ c.hn8 b, hb⟩ (Pm *ᵥ v)
          (Pm *ᵥ w)
        show ((δ g : D) : G) * cT (Pm *ᵥ v) (Pm *ᵥ w) * ((δ g : D) : G)⁻¹ =
          cT (Pm *ᵥ (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
            (Pm *ᵥ (((g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w))
        rw [h1, hPm, mulVec_conj, mulVec_conj]
      comm := fun g => N0.comm_z_of_mem_L c (g1.D_le_L (δ g).2)
      z_sq := z_mul_self c
      inter := fun s g h => by
        have hgL : ((δ g : D) : G) ∈ L := g1.D_le_L (δ g).2
        have hLC := AltStdCycTwo.le_cent_single c.ot.std c.ot.cyc
        have hC : z ^ s.val * δG g ∈ centralizer ({z} : Set G) :=
          mul_mem (pow_mem (mem_centralizer_singleton_iff.2 rfl) _) (hLC hgL)
        have hE : z ^ s.val * δG g ∈ E θ c.hn8 := by
          rw [← g1.hH.n0.cent]
          exact Subgroup.mem_inf.2 ⟨h, hC⟩
        have hs : s = 0 := by
          rcases zmod2_cases s with hs | hs
          · exact hs
          · exfalso
            rw [hs, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hE
            apply N0.z_not_mem_L c
            have : z = z * δG g * (δG g)⁻¹ := by group
            rw [this]
            exact mul_mem (E_le_L c.hn8 hE) (inv_mem hgL)
        refine ⟨hs, ?_⟩
        rw [hs, ZMod.val_zero, pow_zero, one_mul] at h
        have h1 : ((δ g : D) : G) ∈ D ⊓ T := Subgroup.mem_inf.2 ⟨(δ g).2, h⟩
        rw [g1.D_inf, mem_bot] at h1
        exact δ.injective (by rw [map_one]; exact Subtype.ext h1) }
  have hrangeδ : δG.range = D := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (δ g).2
    · intro hx
      exact ⟨δ.symm ⟨x, hx⟩, by rw [hδG, MulEquiv.apply_symm_apply]⟩
  refine ⟨psi hdata, hdata.psi_injective, hdata.map_Qm, hdata.psi_tm, ?_, ?_⟩
  · rw [hdata.map_Mm, hrangeδ]
    rfl
  · rw [hdata.range_psi, hrangeδ]
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le ((zpowers_le.2 hzS₀).trans le_sup_right)
        (g1.D_le_S₀.trans le_sup_right))
    · refine sup_le le_sup_left (hS₀le.trans (sup_le (sup_le ?_ ?_) ?_))
      · exact g1.hH.n0.E_le.trans le_sup_left
      · exact le_sup_right.trans le_sup_right
      · exact le_sup_left.trans le_sup_right

theorem map_centralizer {H : Type} [Group H] {Ψ : H →* G} (hinj : Function.Injective Ψ) (y : H) :
    (centralizer ({y} : Set H)).map Ψ = Ψ.range ⊓ centralizer ({Ψ y} : Set G) := by
  ext x
  constructor
  · rintro ⟨y', hy', rfl⟩
    have hy'' : y' ∈ centralizer ({y} : Set H) := hy'
    refine Subgroup.mem_inf.2 ⟨⟨y', rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hy'' ⊢
    rw [← map_mul, ← map_mul, hy'']
  · intro hx
    obtain ⟨⟨y', rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx
    refine ⟨y', ?_, rfl⟩
    show y' ∈ centralizer ({y} : Set H)
    rw [mem_centralizer_singleton_iff] at hx ⊢
    apply hinj
    rw [map_mul, map_mul, hx]

theorem map_inf_centralizer {H : Type} [Group H] {Ψ : H →* G} (hinj : Function.Injective Ψ)
    (K : Subgroup H) (y : H) :
    (K ⊓ centralizer ({y} : Set H)).map Ψ = K.map Ψ ⊓ centralizer ({Ψ y} : Set G) := by
  rw [map_inf_eq _ _ _ hinj, map_centralizer hinj, ← inf_assoc,
    inf_eq_left.2 (map_le_range Ψ K)]

end ModIso

open ModIso

theorem sec4TBFacts_holds : Sec4TBFacts := by
  intro G _ _ L Q n θ z c T S₀ D g1
  obtain ⟨Ψ, hinj, hQ, htm, hM, hTB⟩ := exists_psi c g1
  have hmemTB : ∀ y : T10, Ψ y ∈ TB T S₀ := fun y => hTB ▸ ⟨y, rfl⟩
  have hpre : ∀ x ∈ TB T S₀, ∃ y : T10, Ψ y = x := fun x hx => by
    rw [← hTB] at hx
    exact hx
  have hcard : ∀ K : Subgroup T10, Nat.card (K.map Ψ) = Nat.card K := fun K =>
    card_map_of_injective hinj
  refine ⟨?_, ?_, ?_⟩
  ·
    intro N hN hnorm hexp hcardN hne
    have hNmap : (N.comap Ψ).map Ψ = N := map_comap_eq_self (hTB ▸ hN)
    have hN'n : (N.comap Ψ).Normal := ⟨fun x hx g => by
      show Ψ (g * x * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ (hmemTB g) _ hx⟩
    have hN'e : ∀ x ∈ N.comap Ψ, x ^ 2 = 1 := fun x hx => hinj (by
      rw [map_pow, map_one]
      exact hexp _ hx)
    have hN'c : Nat.card (N.comap Ψ) = 64 := by rw [← hcard, hNmap, hcardN]
    have hN'ne : N.comap Ψ ≠ Qm := fun h => hne (by rw [← hNmap, h, hQ])
    have h1 := normal_e64 _ hN'n hN'e hN'c hN'ne
    rw [← hcard, map_inf_centralizer hinj, hNmap, htm] at h1
    exact h1
  ·
    intro x hx hxT hx2 hc
    obtain ⟨y, rfl⟩ := hpre x hx
    have hyQ : y ∉ Qm := fun h => hxT (hQ ▸ Subgroup.mem_map_of_mem Ψ h)
    have hy2 : y ^ 2 = 1 := hinj (by rw [map_pow, map_one]; exact hx2)
    have hyc : Nat.card (Qm ⊓ centralizer ({y} : Set T10) : Subgroup T10) = 16 := by
      rw [← hcard, map_inf_centralizer hinj, hQ]
      exact hc
    rw [← hM]
    exact Subgroup.mem_map_of_mem Ψ (mem_Mm_of_card y hyQ hy2 hyc)
  ·
    intro x hx hxT hxo hcases
    rw [← hM] at hx
    obtain ⟨y, hyM, rfl⟩ := hx
    have hyQ : y ∉ Qm := fun h => hxT (hQ ▸ Subgroup.mem_map_of_mem Ψ h)
    have hyo : orderOf y = 2 := by rw [← orderOf_injective Ψ hinj y]; exact hxo
    have ey : centralizer ({y} : Set T10) ≃* (TB T S₀ ⊓ centralizer ({Ψ y} : Set G) : Subgroup G) :=
      ((centralizer ({y} : Set T10)).equivMapOfInjective Ψ hinj).trans
        (MulEquiv.subgroupCongr (by rw [map_centralizer hinj, hTB]))
    have et : centralizer ({tm} : Set T10) ≃* (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G) :=
      ((centralizer ({tm} : Set T10)).equivMapOfInjective Ψ hinj).trans
        (MulEquiv.subgroupCongr (by rw [map_centralizer hinj, hTB, htm]))
    have hyc : Nat.card (centralizer {y} : Subgroup T10) = 2 ^ 8 ∨
        Nonempty (centralizer ({y} : Set T10) ≃* centralizer ({tm} : Set T10)) := by
      rcases hcases with h | h
      · left
        rw [Nat.card_congr ey.toEquiv]
        exact h
      · right
        obtain ⟨e⟩ := h
        exact ⟨(ey.trans e).trans et.symm⟩
    obtain ⟨g, hg⟩ := conj_cent y hyM hyQ hyo hyc
    refine ⟨Ψ g, hmemTB g, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← htm]
    rw [mem_centralizer_singleton_iff] at hg ⊢
    rw [← map_mul, ← map_mul, hg]

end CFSG.OddStandard.AltStdSmall4
