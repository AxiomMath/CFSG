module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bVA
public import CFSG.GH74.QTGen4.U42.ModelFrameC

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut

theorem VA_eq_map_Vsub : VA = Vsub.map incl := by
  rw [VA, Vsub, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨sY p, ⟨p, hp, rfl⟩, (sA_eq_incl p).symm⟩
  · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, (sA_eq_incl p).symm⟩

@[expose] noncomputable def hatVEquiv : Vsub ≃* VA :=
  (Subgroup.equivMapOfInjective Vsub incl incl_injective).trans
    (MulEquiv.subgroupCongr VA_eq_map_Vsub.symm)

@[expose] noncomputable def permHatFun (g : ↥P2h) (j : Fin 5) : Fin 5 :=
  Function.invFun ptL (((g : Ah) : P45) (ptL j))

theorem ptL_permHatFun (g : ↥P2h) (j : Fin 5) :
    ptL (permHatFun g j) = ((g : Ah) : P45) (ptL j) := by
  apply ptL_invFun
  have h := (mem_P2h_iff (g : Ah)).mp g.2
  rw [← h]
  exact ⟨ptL j, (mem_L0S_ptL _).mpr ⟨j, rfl⟩, rfl⟩

theorem permHatFun_injective (g : ↥P2h) : Function.Injective (permHatFun g) := by
  intro j k h
  apply ptL_inj
  have h1 := ptL_permHatFun g j
  have h2 := ptL_permHatFun g k
  rw [h] at h1
  exact ((g : Ah) : P45).injective (h1.symm.trans h2)

@[expose] noncomputable def permHat (g : ↥P2h) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (permHatFun g) (Finite.injective_iff_bijective.mp (permHatFun_injective g))

theorem ptL_permHat (g : ↥P2h) (j : Fin 5) :
    ptL (permHat g j) = ((g : Ah) : P45) (ptL j) := ptL_permHatFun g j

theorem permHat_mul (g h : ↥P2h) : permHat (g * h) = permHat g * permHat h := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  simp only [ptL_permHat, Equiv.Perm.mul_apply, Subgroup.coe_mul]

theorem permHat_one : permHat (1 : ↥P2h) = 1 := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  simp [ptL_permHat]

@[expose] noncomputable def permHomHat : ↥P2h →* Equiv.Perm (Fin 5) where
  toFun := permHat
  map_one' := permHat_one
  map_mul' := permHat_mul

theorem permHomHat_apply (g : ↥P2h) : permHomHat g = permHat g := rfl

@[expose] def inclP2 (g : ↥P2) : ↥P2h :=
  ⟨incl (g : Y), by change (g : Y) ∈ P2h.comap incl; rw [comap_P2h]; exact g.2⟩

theorem permHat_inclP2 (g : ↥P2) : permHat (inclP2 g) = permOf g := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  rw [ptL_permHat, ptL_permOf]
  rfl

theorem permHat_fhat : permHat ⟨fhatA, fhatA_mem_P2h⟩ = Equiv.swap 3 4 := by
  apply Equiv.ext
  intro j
  apply ptL_inj
  rw [ptL_permHat]
  apply Fin.ext
  change (fhat (ptL j) : ℕ) = _
  rw [← repL_fhat.2 (ptL j)]
  revert j
  decide +kernel

theorem permHomHat_surjective : Function.Surjective permHomHat := by
  have even : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → ∃ g : ↥P2h, permHomHat g = σ := by
    intro σ hσ
    obtain ⟨g, hg⟩ := thetaF_surjective ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
    refine ⟨inclP2 g, ?_⟩
    rw [permHomHat_apply, permHat_inclP2]
    exact congrArg Subtype.val hg
  intro σ
  by_cases hσ : σ.sign = 1
  · exact even σ hσ
  · have hτ : (Equiv.swap (3 : Fin 5) 4).sign = -1 := Equiv.Perm.sign_swap (by decide)
    have hσ' : (σ * Equiv.swap 3 4).sign = 1 := by
      rw [Equiv.Perm.sign_mul, hτ, (Int.units_eq_one_or _).resolve_left hσ]
      decide
    obtain ⟨g, hg⟩ := even _ hσ'
    refine ⟨g * ⟨fhatA, fhatA_mem_P2h⟩, ?_⟩
    rw [map_mul, hg, permHomHat_apply, permHat_fhat]
    simp

theorem VA_fix {v : Ah} (hv : v ∈ VA) (p : Fin 45) (hp : p ∈ L0S) : (v : P45) p = p := by
  rw [VA_eq_map_Vsub] at hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  exact Vsub_fix hw p hp

theorem ker_permHomHat : permHomHat.ker = VA.subgroupOf P2h := by
  have hle : VA.subgroupOf P2h ≤ permHomHat.ker := by
    intro v hv
    rw [MonoidHom.mem_ker, permHomHat_apply]
    apply Equiv.ext
    intro j
    apply ptL_inj
    rw [ptL_permHat, Equiv.Perm.one_apply]
    exact VA_fix (Subgroup.mem_subgroupOf.mp hv) _ ((mem_L0S_ptL _).mpr ⟨j, rfl⟩)
  have hcardV : Nat.card (VA.subgroupOf P2h) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe VA_le_P2h).toEquiv,
      ← Nat.card_congr hatVEquiv.toEquiv, card_Vsub_eq]
  have hcardK : Nat.card permHomHat.ker = 16 := by
    have h := Subgroup.card_ker_mul_card_range permHomHat
    rw [MonoidHom.range_eq_top.mpr permHomHat_surjective, Subgroup.card_top, card_P2h] at h
    have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h120] at h
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardV, hcardK])).symm

@[expose] noncomputable def psiHat : VA ≃* W5 := hatVEquiv.symm.trans psiEq

theorem psiHat_hatV (v : Vsub) : psiHat (hatVEquiv v) = psiEq v := by
  simp only [psiHat, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem mem_sA_line (j : Fin 5) : sA (ptL j) ∈ VA :=
  Subgroup.subset_closure ⟨ptL j, (mem_L0S_ptL _).mpr ⟨j, rfl⟩, rfl⟩

theorem psiHat_gen (j : Fin 5) (h : sA (ptL j) ∈ VA) :
    psiHat ⟨sA (ptL j), h⟩ = Multiplicative.ofAdd ⟨FV (2 ^ (j : ℕ)), FV_mem _⟩ := by
  have heq : (⟨sA (ptL j), h⟩ : VA) = hatVEquiv ⟨sY (ptL j), mem_sV_gen j⟩ :=
    Subtype.ext (sA_eq_incl _)
  rw [heq, psiHat_hatV, psiEq_apply, psiM_apply, psiF_gen]

theorem psiHat_conj (a : ↥P2h) {x : Ah} (hx : x ∈ VA) :
    psiHat ⟨(a : Ah) * x * (a : Ah)⁻¹, P2h_conj_VA a.2 hx⟩ =
      pact (permHat a) (psiHat ⟨x, hx⟩) := by
  have key : ∀ h : x ∈ VA,
      psiHat ⟨(a : Ah) * x * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ =
        pact (permHat a) (psiHat ⟨x, h⟩) := by
    refine Subgroup.closure_induction
      (p := fun (x : Ah) _ => ∀ h : x ∈ VA,
        psiHat ⟨(a : Ah) * x * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ =
          pact (permHat a) (psiHat ⟨x, h⟩)) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨p, hp, rfl⟩ h
      obtain ⟨j, rfl⟩ := (mem_L0S_ptL p).mp hp
      have e : (a : Ah) * sA (ptL j) * (a : Ah)⁻¹ = sA (ptL (permHat a j)) := by
        rw [sA_conj, ptL_permHat]
      have h1 : psiHat ⟨(a : Ah) * sA (ptL j) * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ =
          psiHat ⟨sA (ptL (permHat a j)), mem_sA_line _⟩ :=
        congrArg psiHat (Subtype.ext e)
      rw [h1, psiHat_gen (permHat a j), psiHat_gen j, pact_ofAdd]
      exact congrArg Multiplicative.ofAdd (Subtype.ext (pw_FV (permHat a) j).symm)
    · intro h
      have e : (⟨(a : Ah) * 1 * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ : VA) = 1 :=
        Subtype.ext (by simp)
      have e' : (⟨(1 : Ah), h⟩ : VA) = 1 := Subtype.ext rfl
      simp only [e, e', map_one]
    · intro x y hx hy hPx hPy h
      have hxa := P2h_conj_VA a.2 hx
      have hya := P2h_conj_VA a.2 hy
      have e : (⟨(a : Ah) * (x * y) * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ : VA) =
          ⟨(a : Ah) * x * (a : Ah)⁻¹, hxa⟩ * ⟨(a : Ah) * y * (a : Ah)⁻¹, hya⟩ :=
        Subtype.ext (by
          show (a : Ah) * (x * y) * (a : Ah)⁻¹ =
            ((a : Ah) * x * (a : Ah)⁻¹) * ((a : Ah) * y * (a : Ah)⁻¹)
          group)
      have e2 : (⟨x * y, h⟩ : VA) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
      rw [e, e2, map_mul, map_mul, hPx hx, hPy hy, map_mul]
    · intro x hx hPx h
      have hxa := P2h_conj_VA a.2 hx
      have e : (⟨(a : Ah) * x⁻¹ * (a : Ah)⁻¹, P2h_conj_VA a.2 h⟩ : VA) =
          (⟨(a : Ah) * x * (a : Ah)⁻¹, hxa⟩ : VA)⁻¹ := Subtype.ext (by
          show (a : Ah) * x⁻¹ * (a : Ah)⁻¹ = ((a : Ah) * x * (a : Ah)⁻¹)⁻¹
          group)
      have e2 : (⟨x⁻¹, h⟩ : VA) = (⟨x, hx⟩ : VA)⁻¹ := Subtype.ext rfl
      rw [e, e2, map_inv, map_inv, hPx hx, map_inv]
  exact key hx

end CFSG.GH74.QTGen4.U42
