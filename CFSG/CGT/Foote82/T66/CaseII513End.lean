module

public import CFSG.CGT.Foote82.T66.CaseII513G10
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.CGT.Foote82.T66.Prop35
public import CFSG.CGT.Foote82.T66.CaseII513Pow

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel
open Equiv Equiv.Perm

namespace CaseII

theorem factorization_51840 : (51840 : ℕ).factorization 2 = 7 := by
  rw [show (51840 : ℕ) = 2 ^ 7 * 405 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem sylow_equiv_of_max {Γ : Type*} [Group Γ] [Finite Γ] {G T : Subgroup Γ} (hTG : T ≤ G)
    (hT2 : IsPGroup 2 ↥T)
    (hmax : ∀ Y : Subgroup Γ, Y ≤ G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥T)
    (P : Sylow 2 ↥G) : Nonempty (↥P ≃* ↥T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sy, hSy⟩ := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm).exists_le_sylow
  have hSyeq : (Sy : Subgroup ↥G) = T.subgroupOf G := by
    refine (Subgroup.eq_of_le_of_card_ge hSy ?_).symm
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv]
    have h1 := hmax ((Sy : Subgroup ↥G).map G.subtype) (Subgroup.map_subtype_le _)
      (Sy.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective G.subtype_injective] at h1
  exact ⟨((Sylow.equiv P Sy).trans (MulEquiv.subgroupCongr hSyeq)).trans
    (Subgroup.subgroupOfEquivOfLe hTG)⟩

theorem exists_comm_inv {m : ℕ} {ζ : Perm (Fin m)} (hζA : ζ ∈ alternatingGroup (Fin m))
    (hζ2 : orderOf ζ = 2) :
    ∃ ζ' : Perm (Fin m), ζ' ∈ alternatingGroup (Fin m) ∧ ζ' * ζ = ζ * ζ' ∧ orderOf ζ' = 2 ∧
      ζ' ∉ Subgroup.zpowers ζ ∧ ∀ i, ζ i = i → ζ' i = i := by
  have hζζ : ζ * ζ = 1 := by rw [← sq, ← hζ2, pow_orderOf_eq_one]
  have hζinv : ∀ x, ζ (ζ x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin m) => f x) hζζ
    exact this
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := ζ) (by rw [hζ2]; norm_num)
  rw [hζ2] at hk
  have hsupp : ζ.support.card = (k + 1) * 2 := by
    rw [← sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul]
  have hk2 : 1 ≤ k := by
    have hsign := sign_of_cycleType ζ
    rw [mem_alternatingGroup.1 hζA, hk, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul] at hsign
    rcases k with _ | k
    · exfalso
      exact absurd hsign (by decide)
    · omega
  have h4 : 4 ≤ ζ.support.card := by omega
  obtain ⟨a, ha⟩ : ∃ a, a ∈ ζ.support := Finset.card_pos.1 (by omega)
  set b := ζ a with hb
  have hba : b ≠ a := mem_support.1 ha
  have hbs : b ∈ ζ.support := by
    rw [mem_support, hb, hζinv]
    exact hba.symm
  obtain ⟨c, hc⟩ : ∃ c, c ∈ (ζ.support.erase a).erase b := by
    apply Finset.card_pos.1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, hbs⟩), Finset.card_erase_of_mem ha]
    omega
  obtain ⟨hcb, hc'⟩ := Finset.mem_erase.1 hc
  obtain ⟨hca, hcs⟩ := Finset.mem_erase.1 hc'
  set d := ζ c with hd
  have hdc : d ≠ c := mem_support.1 hcs
  have hda : d ≠ a := by
    intro h
    apply hcb
    rw [hb, ← h, hd, hζinv]
  have hdb : d ≠ b := by
    intro h
    apply hca
    have := congrArg ζ h
    rwa [hd, hb, hζinv, hζinv] at this
  set ζ' := swap a c * swap b d with hζ'
  have hdisj : ∀ x, swap a c x = x ∨ swap b d x = x := by
    intro x
    by_cases hxa : x = a
    · right
      rw [hxa]
      exact swap_apply_of_ne_of_ne hba.symm hda.symm
    by_cases hxc : x = c
    · right
      rw [hxc]
      exact swap_apply_of_ne_of_ne hcb hdc.symm
    · left
      exact swap_apply_of_ne_of_ne hxa hxc
  have hcomm : swap a c * swap b d = swap b d * swap a c :=
    Equiv.Perm.Disjoint.commute hdisj
  have hζ'a : ζ' a = c := by
    rw [hζ', Perm.mul_apply, swap_apply_of_ne_of_ne hba.symm hda.symm, swap_apply_left]
  refine ⟨ζ', ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_alternatingGroup, hζ', Perm.sign_mul, sign_swap hca.symm, sign_swap hdb.symm]
    decide
  ·
    have e1 : ζ * swap a c * ζ⁻¹ = swap b d := by rw [← swap_apply_apply]
    have e2 : ζ * swap b d * ζ⁻¹ = swap a c := by
      rw [← swap_apply_apply, hb, hd, hζinv, hζinv]
    have hconj : ζ * ζ' * ζ⁻¹ = ζ' := by
      calc ζ * ζ' * ζ⁻¹ = (ζ * swap a c * ζ⁻¹) * (ζ * swap b d * ζ⁻¹) := by rw [hζ']; group
        _ = swap b d * swap a c := by rw [e1, e2]
        _ = ζ' := hcomm.symm
    calc ζ' * ζ = (ζ * ζ' * ζ⁻¹) * ζ := by rw [hconj]
      _ = ζ * ζ' := by group
  · refine orderOf_eq_two_of_mul_self ?_ ?_
    · calc ζ' * ζ' = swap a c * (swap b d * swap a c) * swap b d := by rw [hζ']; group
        _ = swap a c * (swap a c * swap b d) * swap b d := by rw [hcomm]
        _ = (swap a c * swap a c) * (swap b d * swap b d) := by group
        _ = 1 := by rw [swap_mul_self, swap_mul_self, one_mul]
    · intro h
      apply hca
      have := hζ'a
      rw [h, Perm.one_apply] at this
      exact this.symm
  · intro hm
    rcases CaseII.eq_one_or_eq_of_mem_zpowers hζζ hm with h | h
    · apply hca
      have := hζ'a
      rw [h, Perm.one_apply] at this
      exact this.symm
    · apply hcb
      have := hζ'a
      rw [h] at this
      exact this.symm
  · intro i hi
    have hia : i ≠ a := fun h => mem_support.1 ha (h ▸ hi)
    have hib : i ≠ b := fun h => mem_support.1 hbs (h ▸ hi)
    have hic : i ≠ c := fun h => mem_support.1 hcs (h ▸ hi)
    have hid : i ≠ d := by
      intro h
      apply hic
      have := congrArg ζ h
      rw [hi, hd, hζinv] at this
      exact this
    rw [hζ', Perm.mul_apply, swap_apply_of_ne_of_ne hib hid, swap_apply_of_ne_of_ne hia hic]

section Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {G : Subgroup (GLV V)} {m : ℕ}
  (e : ↥G ≃* alternatingGroup (Fin m))

abbrev iotaA : ↥G →* Perm (Fin m) := (alternatingGroup (Fin m)).subtype.comp e.toMonoidHom

theorem iotaA_injective : Function.Injective (iotaA e) :=
  (alternatingGroup (Fin m)).subtype_injective.comp e.injective

theorem iotaA_mem (g : ↥G) : iotaA e g ∈ alternatingGroup (Fin m) := (e g).2

theorem iotaA_symm {σ : Perm (Fin m)} (hσ : σ ∈ alternatingGroup (Fin m)) :
    iotaA e (e.symm ⟨σ, hσ⟩) = σ := by
  simp

abbrev imgA (H : Subgroup (GLV V)) : Subgroup (Perm (Fin m)) := (H.subgroupOf G).map (iotaA e)

theorem mem_imgA {H : Subgroup (GLV V)} {σ : Perm (Fin m)} :
    σ ∈ imgA e H ↔ ∃ g : ↥G, (g : GLV V) ∈ H ∧ iotaA e g = σ := by
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem imgA_inf_centralizer (t : ↥G) :
    imgA e (G ⊓ Subgroup.centralizer ({(t : GLV V)} : Set (GLV V))) =
      alternatingGroup (Fin m) ⊓ Subgroup.centralizer ({iotaA e t} : Set (Perm (Fin m))) := by
  ext σ
  rw [mem_imgA]
  constructor
  · rintro ⟨g, ⟨-, hg⟩, rfl⟩
    refine ⟨iotaA_mem e g, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hc : (g : GLV V) * t = t * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hc' : g * t = t * g := Subtype.ext hc
    rw [← map_mul, ← map_mul, hc']
  · rintro ⟨hA, hc⟩
    refine ⟨e.symm ⟨σ, hA⟩, ⟨(e.symm ⟨σ, hA⟩).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      iotaA_symm e hA⟩
    have hc' : iotaA e (e.symm ⟨σ, hA⟩ * t) = iotaA e (t * e.symm ⟨σ, hA⟩) := by
      rw [map_mul, map_mul, iotaA_symm]
      exact Subgroup.mem_centralizer_singleton_iff.1 hc
    exact congrArg Subtype.val (iotaA_injective e hc')

theorem isComponentOf_imgA {L K : Subgroup (GLV V)} (hL : L ≤ G) (hK : K ≤ G)
    (h : IsComponentOf L K) : IsComponentOf (imgA e L) (imgA e K) := by
  rw [← CFSG.Assembly.isComponentOf_iff_open] at h ⊢
  have h' : CFSG.Assembly.IsComponentOf (L.subgroupOf G) (K.subgroupOf G) := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff G.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hK]
    exact h
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff (iotaA_injective e)).2 h'

end Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem false_of_alt {m : ℕ} (e : ↥G ≃* alternatingGroup (Fin m)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z' : ↥G := ⟨z, c.z_mem_G⟩ with hz'
  set ζ := iotaA e z' with hζ
  have hζA : ζ ∈ alternatingGroup (Fin m) := iotaA_mem e z'
  have hζ2 : orderOf ζ = 2 := by
    rw [hζ, orderOf_injective (iotaA e) (iotaA_injective e) z', Subgroup.orderOf_mk, c.orderOf_z]
  have hcomp : IsComponentOf (imgA e L)
      (alternatingGroup (Fin m) ⊓ Subgroup.centralizer ({ζ} : Set (Perm (Fin m)))) := by
    rw [hζ, ← imgA_inf_centralizer e z']
    exact isComponentOf_imgA e c.L_le_G inf_le_left c.isComponentOf_Cz
  have hR : IsPGroup 2 ↥(Subgroup.zpowers ζ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hζ2, pow_one])
  have hCR : Subgroup.centralizer ((Subgroup.zpowers ζ : Subgroup (Perm (Fin m))) :
      Set (Perm (Fin m))) = Subgroup.centralizer ({ζ} : Set (Perm (Fin m))) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨-, hLeq⟩ := eq_altOn_of_isComponentOf hR (by rw [hCR]) (by rw [hCR]; exact inf_le_right)
    hcomp
  obtain ⟨ζ', hζ'A, hζ'c, hζ'2, hζ'z, hζ'F⟩ := exists_comm_inv hζA hζ2
  have hcentF : ∀ σ ∈ imgA e L, σ * ζ' = ζ' * σ := by
    intro σ hσ
    rw [hLeq] at hσ
    refine Equiv.Perm.Disjoint.commute fun i => ?_
    by_cases hi : i ∈ {i : Fin m | ∀ r ∈ Subgroup.zpowers ζ, r i = i}
    · right
      exact hζ'F i (hi ζ (Subgroup.mem_zpowers ζ))
    · left
      exact (mem_fixingSubgroup_iff _).1 hσ.2 i hi
  set k' : ↥G := e.symm ⟨ζ', hζ'A⟩ with hk'
  have hk'ι : iotaA e k' = ζ' := iotaA_symm e hζ'A
  have hk'K : (k' : GLV V) ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    refine ⟨k'.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have h1 := hcentF (iotaA e ⟨l, c.L_le_G hl⟩) ((mem_imgA e).2 ⟨⟨l, c.L_le_G hl⟩, hl, rfl⟩)
    rw [← hk'ι, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (iotaA_injective e h1)
  have hk'z : Commute z (k' : GLV V) := by
    have h1 : iotaA e (z' * k') = iotaA e (k' * z') := by
      rw [map_mul, map_mul, hk'ι, ← hζ]
      exact hζ'c.symm
    exact congrArg Subtype.val (iotaA_injective e h1)
  have hk'2 : orderOf (k' : GLV V) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective (iotaA e) (iotaA_injective e) k', hk'ι, hζ'2]
  have hk'n : (k' : GLV V) ∉ Subgroup.zpowers z := by
    intro hm
    apply hζ'z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have h1 : z' ^ n = k' := Subtype.ext (by rw [Subgroup.coe_zpow, hn])
    rw [← hk'ι, ← h1, map_zpow, hζ]
  have h2 := CFSG.GroupTheory.two_le_pRank_of_commute c.z_mem_K hk'K c.orderOf_z hk'2 hk'z hk'n
  rw [c.rank] at h2
  omega

theorem prop513 (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) (hG2 : CaseIIG2)
    (hG9 : CaseIIG9) (hG10 : CaseIIG10) (hG12 : CaseIIG12) (h511a : CaseIILemma511a) :
    ∀ x ∈ G, x * z * x⁻¹ ∉ HH G L v := by
  intro x hxG hxH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, d⟩ := c.exists_gd hG1
  obtain ⟨P, pd, h4⟩ := d.exists_pd hs haut hG1 hG9 hG12 hxG hxH
  obtain ⟨T, hTH₁, hT2, hTc, -, -⟩ := d.exists_T
  rw [c.card_H₁, factorization_51840] at hTc
  have hTG : T ≤ G := hTH₁.trans c.H₁_le_G
  have h128 : 128 ∣ Nat.card ↥G := by
    rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← hTc]
    exact Subgroup.card_dvd_of_le hTG
  have hmaxG := card_le_of_G10 hG10 pd.le pd.isPGroup pd.card pd.iso pd.card_center pd.z_mem
    c.orderOf_z pd.sylow h128
  obtain ⟨hGE, hGq⟩ := c.std.quasisimple h4
  have hsyl : ∀ (P' : Sylow 2 ↥G) (Q : Sylow 2 ↥(alternatingGroup (Fin 10))),
      Nonempty (↥P' ≃* ↥Q) := by
    intro P' Q
    obtain ⟨e₁⟩ := sylow_equiv_of_max hTG hT2 (fun Y hY hY2 => by rw [hTc]; exact hmaxG Y hY hY2) P'
    set TO := (T.subgroupOf H₁).map ψ.toMonoidHom with hTO
    have hTOc : Nat.card ↥TO =
        2 ^ (Nat.card ↥(orthogonalMinus 2 (ZMod 2) 1 1)).factorization 2 := by
      rw [hTO, Subgroup.card_map_of_injective ψ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH₁).toEquiv, hTc,
        ← Nat.card_congr ψ.toEquiv, c.card_H₁, factorization_51840]
    obtain ⟨e₂⟩ := hG2.1 (Sylow.ofCard TO hTOc) Q
    exact ⟨((e₁.trans (Subgroup.subgroupOfEquivOfLe hTH₁).symm).trans
      ((T.subgroupOf H₁).equivMapOfInjective _ ψ.injective)).trans e₂⟩
  obtain ⟨α, β, ad⟩ := c.exists_ad hs
  have hL := c.data.L_iso
  obtain ⟨ℓ₀, hℓ₀⟩ := ad.α_surj CFSG.ComponentClassification.RankTwoAlt.a6c012
  have hfin := ad.finrank_c₀ hL hℓ₀
  have hord : orderOf (ℓ₀ : GLV V) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (ad.αe hL) ℓ₀, ad.αe_apply, hℓ₀]
    exact orderOf_eq_prime (by decide) (by decide)
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥G)) := by
    have h1 := c.std.extremal.setup.odd_card_centralizer_layerIn
    rw [← hGE] at h1
    refine h1.of_dvd_nat ?_
    have hle : (Subgroup.center ↥G).map G.subtype ≤
        G ⊓ Subgroup.centralizer (G : Set (GLV V)) := by
      rintro _ ⟨c', hc', rfl⟩
      refine ⟨c'.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have := Subgroup.mem_center_iff.1 hc' ⟨g, hg⟩
      exact congrArg Subtype.val this
    rw [← Subgroup.card_map_of_injective G.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hCG : G ⊓ Subgroup.centralizer (G : Set (GLV V)) ≤ (Subgroup.center ↥G).map G.subtype :=
    fun x hx => mem_center_map_iff.2 ⟨hx.1, fun p hp => Subgroup.mem_centralizer_iff.1 hx.2 p hp⟩
  rcases h511a V G G L z ℓ₀ le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
      (by rw [Subgroup.relIndex_self]; norm_num) hCG hGq hZodd c.z_mem_G c.orderOf_z
      c.isComponentOf_Cz hL (c.isAltNaturalModule hs) c.std.extremal.setup.irr ℓ₀.2 hord hfin
      hsyl with h | h
  · obtain ⟨e⟩ := h
    exact c.false_of_alt e
  · obtain ⟨e⟩ := h
    exact c.false_of_alt e

end Ctx

end CaseII

end CFSG.CGT.Foote82
