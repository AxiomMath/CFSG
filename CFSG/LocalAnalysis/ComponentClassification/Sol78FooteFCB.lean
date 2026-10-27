module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFCBase
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.Dihedral.Glauberman.DicksonMaxTables

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.GorensteinWalter

theorem card_sylow_two_alt7 (P : Sylow 2 (alternatingGroup (Fin 7))) :
    Nat.card (P : Subgroup (alternatingGroup (Fin 7))) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [Sylow.card_eq_multiplicity P, h, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (315 : ℕ))]

private theorem commute_of_mul_self {G : Type*} [Group G] {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v * (u * v) = 1) : u * v = v * u := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
    _ = v * u := by rw [mul_inv_rev, hu', hv']

theorem mem_of_centralizes_kleinFour_alt7 {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 7)) {W : Subgroup Y} (hW : IsKleinFour W) {a : Y}
    (haa : a * a = 1) (haW : ∀ w ∈ W, a * w = w * a) : a ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra haW'
  have hW2 : ∀ v ∈ W, v * v = 1 := fun v hv => by
    rw [← sq]
    exact FooteLit.sq_eq_one_of_isKleinFour hW hv
  obtain ⟨F, -, -, -, hF2, hF8⟩ :=
    AutL2Facts.exists_e8_of_centralizing W hW2 hW.card_four haa haW' haW
  set F' := F.map e.toMonoidHom with hF'
  have hF'8 : Nat.card F' = 8 := by rw [hF', card_map_of_injective e.injective, hF8]
  have hF'2 : ∀ x ∈ F', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hF2 x hx, map_one]
  have hF'p : IsPGroup 2 F' := IsPGroup.of_card (n := 3) (by rw [hF'8]; norm_num)
  obtain ⟨P, hFP⟩ := hF'p.exists_le_sylow
  have hFP' : F' = P :=
    Subgroup.eq_of_le_of_card_ge hFP (by rw [card_sylow_two_alt7 P, hF'8])
  have hPc : ∀ u v : (P : Subgroup (alternatingGroup (Fin 7))), u * v = v * u := by
    intro u v
    have hu : (u : alternatingGroup (Fin 7)) ∈ F' := hFP'.symm ▸ u.2
    have hv : (v : alternatingGroup (Fin 7)) ∈ F' := hFP'.symm ▸ v.2
    exact Subtype.ext (commute_of_mul_self (hF'2 _ hu) (hF'2 _ hv) (hF'2 _ (mul_mem hu hv)))
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := AutL2Facts.exists_noncomm_two_subgroup_a7
  obtain ⟨Q, hHQ⟩ := hH2.exists_le_sylow
  set φ := Sylow.equiv Q P with hφ
  apply hxy
  have h1 := hPc (φ ⟨x, hHQ hx⟩) (φ ⟨y, hHQ hy⟩)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (φ.injective h1)

theorem mem_of_centralizes_kleinFour_psl2
    {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F) {W : Subgroup Y} (hW : IsKleinFour W)
    {a : Y} (haW : ∀ w ∈ W, a * w = w * a) : a ∈ W := by
  set ι : Y →* PGL2 F :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp e.toMonoidHom with hι
  have hι : Function.Injective ι :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hW' : IsKleinFour (W.map ι) := isKleinFour_map_of_injective hι hW
  have hc : ι a ∈ centralizer ((W.map ι : Subgroup (PGL2 F)) : Set (PGL2 F)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, haW w hw]
  rw [pgl2_kleinFour_centralizer_eq_self F hF _ hW'] at hc
  obtain ⟨w, hw, hwa⟩ := hc
  rwa [← hι hwa]

theorem two_ne_zero_of_card {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hF
    have := Finite.one_lt_card (α := F)
    omega
  have hcard : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hcard
  intro h2
  have hp2' : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2' with h | h
  · exact hp.ne_one h
  · exact hp2 h

theorem conj_injective_of_footeSimpleType {Y : Type} [Group Y] [Finite Y]
    (hY : FooteSimpleType Y) : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  have hzc : ∀ y : Y, z * y = y * z := fun y => by
    have h := congrArg (fun φ : MulAut Y => φ y) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc z * y = z * y * z⁻¹ * z := by group
      _ = y * z := by rw [h]
  rw [mem_bot]
  rcases hY with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · have h1 : ((e z : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 1 := by
      apply LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
        (by rw [Fintype.card_fin]; norm_num)
      intro g hg
      have h2 := hzc (e.symm ⟨g, hg⟩)
      have h3 := congrArg (fun y => ((e y : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) h2
      simpa using h3
    exact e.injective (by rw [map_one]; exact Subtype.ext h1)
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    have hsimple : IsSimpleGroup (PSL2 F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; omega)
    have hcen : e z ∈ center (PSL2 F) := by
      rw [mem_center_iff]
      intro g
      have h2 := hzc (e.symm g)
      have h3 := congrArg e h2
      simpa using h3.symm
    have hbot : center (PSL2 F) = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (center (PSL2 F)) with h | h
      · exact h
      · exfalso
        obtain ⟨H, ⟨eH⟩⟩ := Glauberman.Dickson.QuatTable.exists_alternatingFour_subgroup (F := F)
          (two_ne_zero_of_card hp hp2 hF)
        set s : alternatingGroup (Fin 4) :=
          ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
        set t : alternatingGroup (Fin 4) :=
          ⟨Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
        have hst : s * t ≠ t * s := fun h' => absurd (congrArg Subtype.val h') (by decide)
        apply hst
        have h1 := mem_center_iff.mp (h ▸ mem_top ((eH.symm t : H) : PSL2 F))
          ((eH.symm s : H) : PSL2 F)
        have h2 : eH.symm s * eH.symm t = eH.symm t * eH.symm s := Subtype.ext h1
        rw [← map_mul, ← map_mul] at h2
        exact eH.symm.injective h2
    rw [hbot, mem_bot] at hcen
    exact e.injective (by rw [hcen, map_one])

end CFSG.ComponentClassification.Sol78
