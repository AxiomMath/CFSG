module

public import CFSG.LargeExtraspecial.S14Perfect
public import CFSG.LargeExtraspecial.S14Early

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

theorem mulAut_comm_of_isCyclic {K : Type*} [Group K] [IsCyclic K] (f f' : MulAut K) :
    f * f' = f' * f := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic f.toMonoidHom
  obtain ⟨m', hm'⟩ := MonoidHom.map_cyclic f'.toMonoidHom
  ext x
  change f (f' x) = f' (f x)
  have e1 : f (f' x) = (x ^ m') ^ m := by
    rw [show f (f' x) = f.toMonoidHom (f'.toMonoidHom x) from rfl, hm', hm]
  have e2 : f' (f x) = (x ^ m) ^ m' := by
    rw [show f' (f x) = f'.toMonoidHom (f.toMonoidHom x) from rfl, hm, hm']
  rw [e1, e2, ← zpow_mul, ← zpow_mul, mul_comm]

theorem centralizes_of_perfect_of_card_dvd_three {X : Type*} [Group X] {O R : Subgroup X}
    [O.Normal] (hO : Nat.card O ∣ 3) (hR : ⁅R, R⁆ = R) :
    ∀ r ∈ R, ∀ x ∈ O, r * x * r⁻¹ = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic O := isCyclic_of_card_dvd_prime hO
  set φ : X →* MulAut O := MulAut.conjNormal
  have hle : ⁅R, R⁆ ≤ φ.ker := commutator_le.mpr fun a _ b _ => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_comm_of_isCyclic _ _
  intro r hr x hx
  have h1 : φ r = 1 := (hR ▸ hle) hr
  have h2 := congrArg (fun f : MulAut O => ((f ⟨x, hx⟩ : O) : X)) h1
  simpa [φ, MulAut.conjNormal_apply] using h2

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem commutator_subgroupOf_Mbar {g : G} {t : S.O}
    (hR : ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t) :
    ⁅(Rbar S g t).subgroupOf S.Mbar, (Rbar S g t).subgroupOf S.Mbar⁆ =
      (Rbar S g t).subgroupOf S.Mbar := by
  have hmap : ((Rbar S g t).subgroupOf S.Mbar).map S.Mbar.subtype = Rbar S g t := by
    rw [subgroupOf_map_subtype, inf_of_le_left Rbar_le_Mbar]
  apply map_injective S.Mbar.subtype_injective
  rw [map_commutator, hmap, hR]

theorem oddCore_Mbar_eq_bot {g : G} {t : S.O} (hSt : Stage S g t)
    (hRp : ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t) : timmesfeldOddCore S.Mbar = ⊥ := by
  have H := hSt.hyp4
  have C := hSt.cons
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  have hn : 4 < S.width := by have := hSt.six_le_width; omega
  have h3 := S5.card_oddCore_dvd_three H hNo C hn
  have hON : (timmesfeldOddCore S.Mbar).Normal := S5.timmesfeldOddCore_normal S.Mbar
  have hcent := centralizes_of_perfect_of_card_dvd_three h3 (commutator_subgroupOf_Mbar hRp)
  by_contra hne
  set K := (timmesfeldOddCore S.Mbar).map S.Mbar.subtype with hKdef
  have hcardK : Nat.card K = Nat.card (timmesfeldOddCore S.Mbar) :=
    card_map_of_injective S.Mbar.subtype_injective
  have hK : K ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective _ S.Mbar.subtype_injective).mp h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic K := isCyclic_of_card_dvd_prime (hcardK ▸ h3)
  have hodd : Odd (Nat.card K) := hcardK ▸ S5.odd_card_timmesfeldOddCore S.Mbar
  have hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ K, s * x * s⁻¹ ∈ K := fun s hs x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨s, S.Lbar_le_Mbar g hs⟩ * y * (⟨s, S.Lbar_le_Mbar g hs⟩ : S.Mbar)⁻¹,
      hON.conj_mem y hy _, rfl⟩
  apply (S5.timmesfeld_5_3 H hNo C (map_subtype_le _) hcyc hodd hK hnorm).2
  rw [commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  intro s hs
  have hsR : (⟨s, S.Lbar_le_Mbar g hs⟩ : S.Mbar) ∈ (Rbar S g t).subgroupOf S.Mbar :=
    mem_subgroupOf.mpr (Lbar_le_Rbar hSt.mem hs)
  have h1 := congrArg Subtype.val (hcent _ hsR y hy)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  change s * (y : S.O) = (y : S.O) * s
  calc s * (y : S.O) = (s * (y : S.O) * s⁻¹) * s := by group
    _ = (y : S.O) * s := by rw [h1]

theorem center_layer_eq_bot (hO : timmesfeldOddCore S.Mbar = ⊥) :
    center (timmesfeldLayer S.Mbar) = ⊥ := by
  set E := timmesfeldLayer S.Mbar
  have hEn : E.Normal := CFSG.ComponentClassification.Layer.normal S.Mbar
  set Z := (center E).map E.subtype with hZdef
  have hZn : Z.Normal := ⟨fun x hx m => by
    obtain ⟨e, he, rfl⟩ := hx
    have hme : m * (e : S.Mbar) * m⁻¹ ∈ E := hEn.conj_mem _ e.2 m
    refine ⟨⟨_, hme⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at he ⊢
    intro e'
    apply Subtype.ext
    have h1 : m⁻¹ * (e' : S.Mbar) * m ∈ E := by simpa using hEn.conj_mem _ e'.2 m⁻¹
    have h2 := congrArg Subtype.val (he ⟨_, h1⟩)
    simp only [Subgroup.coe_mul] at h2 ⊢
    calc (e' : S.Mbar) * (m * (e : S.Mbar) * m⁻¹) =
        m * ((m⁻¹ * (e' : S.Mbar) * m) * (e : S.Mbar)) * m⁻¹ := by group
      _ = m * ((e : S.Mbar) * (m⁻¹ * (e' : S.Mbar) * m)) * m⁻¹ := by rw [h2]
      _ = m * (e : S.Mbar) * m⁻¹ * (e' : S.Mbar) := by group⟩
  have hZnil : Group.IsNilpotent Z :=
    (Group.isNilpotent_congr ((center E).equivMapOfInjective _ E.subtype_injective)).mp
      inferInstance
  have hZF : Z ≤ timmesfeldFitting S.Mbar := le_sSup ⟨hZn, hZnil⟩
  have hZO := hZF.trans (S5.fitting_le_oddCore S)
  rw [hO] at hZO
  exact (map_eq_bot_iff_of_injective _ E.subtype_injective).mp (le_bot_iff.mp hZO)

theorem claim_14_6 [IsSimpleGroup G] (hCE : CentralExtInput.{0})
    {g : G} {t : S.O} {c : Config} (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) : IsSimpleGroup (Mbar0 S) := by
  have H := hSt.hyp4
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  have hn : 4 < S.width := by have := hSt.six_le_width; omega
  obtain ⟨-, hq, hF⟩ := S5.timmesfeld_5_5 hCE (irr_of_not_isReducible hSt.irr) H hNo hSt.cons
    (S45Q.hyp45Q H hSt.cons) hn
  have hO := oddCore_Mbar_eq_bot hSt (rbarPerfectStmt_of hCE G S g t c hSt hocc hext)
  have hFE : Mbar0 S = timmesfeldLayer S.Mbar := by
    change timmesfeldFStar S.Mbar = _
    rw [hF, hO, bot_sup_eq]
  have hEs : IsSimpleGroup (timmesfeldLayer S.Mbar) :=
    (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq
      (center_layer_eq_bot hO)).trans QuotientGroup.quotientBot)).mp hq.2
  exact (MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr hFE)).mpr hEs

end CFSG.LargeExtraspecial.S14
