module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreElem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem eq_inl_of_right {x : PGammaL2 F} (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left :=
  SemidirectProduct.ext rfl (by rw [hx]; rfl)

theorem klein_centralizer
    (hodd : IsOddPrimePower (Nat.card F)) {E : Subgroup (PGammaL2 F)}
    (hE1 : ∀ e ∈ E, e.right = 1) (hE4 : Nat.card E = 4) (hEsq : ∀ e ∈ E, e ^ 2 = 1)
    {x : PGammaL2 F} (hx1 : x.right = 1) (hxE : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  set V : Subgroup (PGL2 F) := E.comap SemidirectProduct.inl
  have hVE : V.map SemidirectProduct.inl = E := by
    refine map_comap_eq_self fun e he => ⟨e.left, (eq_inl_of_right (hE1 e he)).symm⟩
  have hV4 : Nat.card V = 4 := by
    rw [← hE4, ← hVE, card_map_of_injective SemidirectProduct.inl_injective]
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hV4]; norm_num
  have hV : IsKleinFour V := ⟨hV4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    fun g hg => by
      have h2 : (g : PGL2 F) ^ 2 = 1 := SemidirectProduct.inl_injective (by
        rw [map_pow, map_one]
        exact hEsq _ (show (SemidirectProduct.inl (g : PGL2 F) : PGammaL2 F) ∈ E from g.2))
      exact orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])) hg⟩
  have hc := pgl2_kleinFour_centralizer_eq_self F hodd V hV
  have hxV : x.left ∈ centralizer (V : Set (PGL2 F)) := by
    rw [mem_centralizer_iff]
    intro v hv
    have h := hxE _ (show (SemidirectProduct.inl v : PGammaL2 F) ∈ E from hv)
    rw [eq_inl_of_right hx1, ← map_mul, ← map_mul] at h
    exact (SemidirectProduct.inl_injective h).symm
  rw [hc] at hxV
  rw [eq_inl_of_right hx1]
  exact hxV

theorem exists_klein (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) :
    ∃ a b : PGammaL2 F, a ∈ (T : Subgroup (PSL2 F)).map (incl F) ∧
      b ∈ (T : Subgroup (PSL2 F)).map (incl F) ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a ∧
      a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a := by
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hodd T
  obtain ⟨ha, hb, hab, hne⟩ := HarrisLit.dihedral_commuting_involutions hm
  set a := DihedralGroup.r (1 : ZMod (2 ^ m)) ^ 2 ^ (m - 1)
  set b := DihedralGroup.sr (0 : ZMod (2 ^ m))
  have hinj : Function.Injective fun g : DihedralGroup (2 ^ m) =>
      incl F ((e.symm g : ↥(T : Subgroup (PSL2 F))) : PSL2 F) :=
    (incl_injective F).comp (Subtype.val_injective.comp e.symm.injective)
  have hmul : ∀ g h : DihedralGroup (2 ^ m),
      incl F ((e.symm (g * h) : ↥(T : Subgroup (PSL2 F))) : PSL2 F) =
        incl F ((e.symm g : ↥(T : Subgroup (PSL2 F))) : PSL2 F) *
          incl F ((e.symm h : ↥(T : Subgroup (PSL2 F))) : PSL2 F) := by
    intro g h
    rw [map_mul, Subgroup.coe_mul, map_mul]
  have hone : incl F ((e.symm 1 : ↥(T : Subgroup (PSL2 F))) : PSL2 F) = 1 := by
    rw [map_one, Subgroup.coe_one, map_one]
  have ha2' : a ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ha)
  have hb2' : b ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hb)
  refine ⟨_, _, ⟨_, (e.symm a).2, rfl⟩, ⟨_, (e.symm b).2, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_two, ← hmul, ← pow_two, ha2', hone]
  · rw [pow_two, ← hmul, ← pow_two, hb2', hone]
  · rw [← hmul, ← hmul, hab]
  · intro h
    rw [← hone] at h
    have := hinj h
    rw [this, orderOf_one] at ha
    norm_num at ha
  · intro h
    rw [← hone] at h
    have := hinj h
    rw [this, orderOf_one] at hb
    norm_num at hb
  · intro h
    exact hne (hinj h).symm

theorem mem_of_centralizes
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F))
    {x : PGammaL2 F} (hx1 : x.right = 1)
    (hx : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), x * d = d * x) :
    x ∈ (T : Subgroup (PSL2 F)).map (incl F) := by
  obtain ⟨a, b, haD, hbD, ha2, hb2, hab, ha1, hb1, hba⟩ := exists_klein hodd T
  have hle : zpowers a ⊔ zpowers b ≤ (T : Subgroup (PSL2 F)).map (incl F) :=
    sup_le (zpowers_le.mpr haD) (zpowers_le.mpr hbD)
  have hright : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), d.right = 1 := by
    rintro _ ⟨t, -, rfl⟩
    rfl
  exact hle (klein_centralizer hodd (fun e he => hright e (hle he))
    (card_E4 ha2 hb2 hab ha1 hb1 hba) (elem_E4 ha2 hb2 hab).sq_eq_one hx1
    fun e he => hx e (hle he))

end CFSG.ComponentClassification.HSDihedral.Model
