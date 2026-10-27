module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniModel
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeField
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer

section Iota

theorem exists_conj_unitriangular_le_of_card_two
    {Q : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))} (hQ : IsPGroup 2 Q)
    (hQc : 2 ^ 6 ≤ Nat.card Q) :
    ∃ h : SpecialLinearGroup (Fin 4) (ZMod 2), ∀ y ∈ unitriangular 4 (ZMod 2), h * y * h⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (by norm_num : 1 ≤ 4)
  obtain ⟨P₁, hQP⟩ := hQ.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 4) (ZMod 2)) U₀ P₁
  have hUc : Nat.card (U₀ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) = 2 ^ 6 := by
    rw [hU₀, card_unitriangular, Nat.card_zmod]
  have hPc : Nat.card (P₁ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity U₀, hUc]
  have hQP' : Q = (P₁ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) :=
    eq_of_le_of_card_ge hQP (by rw [hPc]; exact hQc)
  refine ⟨h, fun y hy => ?_⟩
  rw [hQP', ← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv, MulAut.smul_def, MulAut.conj_apply, hU₀]
  convert hy using 1
  group

@[expose] def veeIota : SpecialLinearGroup (Fin 4) (ZMod 2) →* SpecialLinearGroup (Fin 4) F4 :=
  SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F4)

theorem coe_veeIota_apply (y : SpecialLinearGroup (Fin 4) (ZMod 2)) (i j : Fin 4) :
    ((veeIota y : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) i j =
      ZMod.castHom (dvd_refl 2) F4 ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) := rfl

theorem castHom_F4_injective : Function.Injective (ZMod.castHom (dvd_refl 2) F4) := by
  intro a b h
  revert a b
  decide

theorem veeIota_injective : Function.Injective veeIota := by
  intro y z h
  ext i j
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 4) F4 =>
    (x : Matrix (Fin 4) (Fin 4) F4) i j) h
  simp only [coe_veeIota_apply] at h1
  exact castHom_F4_injective h1

theorem veeFrob_veeIota (y : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    veeFrob (veeIota y) = veeIota y := by
  ext i j
  rw [coe_veeFrob, Matrix.map_apply, coe_veeIota_apply]
  generalize (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = a
  revert a
  decide

theorem exists_veeIota_eq_of_veeFrob_eq {x : SpecialLinearGroup (Fin 4) F4} (hx : veeFrob x = x) :
    ∃ y, veeIota y = x := by
  have hent : ∀ i j, ∃ b : ZMod 2, ZMod.castHom (dvd_refl 2) F4 b =
      (x : Matrix (Fin 4) (Fin 4) F4) i j := by
    intro i j
    have h1 := congrArg (fun z : SpecialLinearGroup (Fin 4) F4 =>
      (z : Matrix (Fin 4) (Fin 4) F4) i j) hx
    simp only [coe_veeFrob, Matrix.map_apply] at h1
    generalize (x : Matrix (Fin 4) (Fin 4) F4) i j = a at h1 ⊢
    revert a
    decide
  choose M hM using hent
  have hdet : (Matrix.of M).det = 1 := by
    apply castHom_F4_injective
    rw [map_one, RingHom.map_det]
    have h1 : (ZMod.castHom (dvd_refl 2) F4).mapMatrix (Matrix.of M) =
        (x : Matrix (Fin 4) (Fin 4) F4) := by
      ext i j
      exact hM i j
    rw [h1]
    exact x.2
  refine ⟨(⟨Matrix.of M, hdet⟩ : SpecialLinearGroup (Fin 4) (ZMod 2)), ?_⟩
  ext i j
  exact hM i j

end Iota

section Norm

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_unitriangular_of_sylow {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) {W₁ Nt : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8)
    (hV : Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ 4)
    (D : Nt →* SpecialLinearGroup (Fin 4) F4) (hDk : ∀ n, D n = 1 ↔ (n : G) ∈ W₁)
    (hDt : ∀ n m : Nt, (m : G) = t * n * t⁻¹ → D m = veeFrob (D n))
    {S₀ : Subgroup G} (hS₀ : IsLFiveFieldSylow L t Nt S₀) :
    ∃ g : SpecialLinearGroup (Fin 4) F4, veeFrob g = g ∧
      ∀ n : Nt, (n : G) ∈ S₀ ↔ g⁻¹ * D n * g ∈ unitriangular 4 F4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS₀p, hS₀N, hS₀syl, -, Q₀, hQ₀L, hQ₀c, hQ₀S₀⟩ := hS₀
  have hQ₀N : Q₀ ≤ Nt := hQ₀S₀.trans hS₀N
  set Q := (Q₀.subgroupOf Nt).map D with hQdef
  have hQfix : ∀ x ∈ Q, veeFrob x = x := by
    rintro _ ⟨q, hq, rfl⟩
    have hqt : (q : G) = t * q * t⁻¹ := by
      have h := (mem_centralizer_iff.1 htC) _ (hQ₀L (mem_subgroupOf.1 hq))
      calc (q : G) = q * t * t⁻¹ := by group
        _ = t * q * t⁻¹ := by rw [h]
    exact (hDt q q hqt).symm
  have hQc : 2 ^ 6 ≤ Nat.card Q := by
    set Q₀' := Q₀.subgroupOf Nt with hQ₀'
    let f : Q₀' →* SpecialLinearGroup (Fin 4) F4 := D.comp Q₀'.subtype
    have hfrange : f.range = Q := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfrange] at h1
    have hQ₀'c : Nat.card Q₀' = 2 ^ 10 :=
      (Nat.card_congr (subgroupOfEquivOfLe hQ₀N).toEquiv).trans hQ₀c
    have hker : Nat.card f.ker ≤ 2 ^ 4 := by
      rw [← hV]
      refine Nat.card_le_card_of_injective (fun x => ⟨(((x : Q₀') : Nt) : G), ?_⟩) ?_
      · have hx1 : D (x : Q₀') = 1 := x.2
        refine mem_inf.2 ⟨(hDk _).1 hx1, mem_centralizer_singleton_iff.2 ?_⟩
        exact (mem_centralizer_iff.1 htC) _ (hQ₀L (mem_subgroupOf.1 (x : Q₀').2))
      · intro a b hab
        have h := congrArg Subtype.val hab
        simp only at h
        exact Subtype.ext (Subtype.ext (Subtype.ext h))
    rw [hQ₀'c] at h1
    have h2 : 2 ^ 6 * 2 ^ 4 ≤ Nat.card Q * 2 ^ 4 := by
      calc 2 ^ 6 * 2 ^ 4 = Nat.card Q * Nat.card f.ker := by rw [← h1]; norm_num
        _ ≤ Nat.card Q * 2 ^ 4 := Nat.mul_le_mul_left _ hker
    exact Nat.le_of_mul_le_mul_right h2 (by norm_num)
  have hQ2 : IsPGroup 2 Q := ((hS₀p.to_le hQ₀S₀).comap_subtype (K := Nt)).map D
  set Q' := Q.comap veeIota with hQ'def
  have hQ'map : Q'.map veeIota = Q := by
    refine map_comap_eq_self ?_
    intro x hx
    exact exists_veeIota_eq_of_veeFrob_eq (hQfix x hx)
  have hQ'c : 2 ^ 6 ≤ Nat.card Q' := by
    rw [← card_map_of_injective veeIota_injective, hQ'map]
    exact hQc
  have hQ'2 : IsPGroup 2 Q' := hQ2.comap_of_injective _ veeIota_injective
  obtain ⟨h, hh⟩ := exists_conj_unitriangular_le_of_card_two hQ'2 hQ'c
  set g := veeIota h with hgdef
  refine ⟨g, veeFrob_veeIota h, ?_⟩
  set P := (S₀.subgroupOf Nt).map D with hPdef
  have hP2 : IsPGroup 2 P := (hS₀p.comap_subtype (K := Nt)).map D
  set P'' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP''def
  have hP''2 : IsPGroup 2 P'' := hP2.map _
  have hgen : ∀ i j : Fin 4, i.val + 1 = j.val →
      ∃ p : P'', (Matrix.SpecialLinearGroup.coeMonoidHom.comp P''.subtype) p =
        1 + single i j 1 := by
    intro i j hij
    have hij' : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := Fin.lt_def.2 (by omega)
    set y := SpecialLinearGroup.transvection hij' (1 : ZMod 2) with hy
    have hyU : y ∈ unitriangular 4 (ZMod 2) := by
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · change (1 + single i j (1 : ZMod 2)) a b = 0
        rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hab), zero_add, single_apply]
        refine ite_eq_right_iff.2 fun h => ?_
        obtain ⟨rfl, rfl⟩ := h
        exact absurd (hab.trans hlt) (lt_irrefl _)
      · change (1 + single i j (1 : ZMod 2)) a a = 1
        rw [Matrix.add_apply, Matrix.one_apply_eq, single_apply]
        have hne : ¬ (i = a ∧ j = a) := by
          rintro ⟨rfl, h2⟩
          exact hij' h2.symm
        simp only [hne, ite_false, add_zero]
    have h1 := hh y hyU
    have h2 : veeIota (h * y * h⁻¹) ∈ Q := h1
    have h3 : g * veeIota y * g⁻¹ ∈ P := by
      rw [hgdef, ← map_inv, ← map_mul, ← map_mul]
      obtain ⟨q, hq, hqe⟩ := h2
      exact ⟨q, mem_subgroupOf.2 (hQ₀S₀ (mem_subgroupOf.1 hq)), hqe⟩
    refine ⟨⟨veeIota y, ⟨_, h3, ?_⟩⟩, ?_⟩
    · change g⁻¹ * (g * veeIota y * g⁻¹) * g⁻¹⁻¹ = veeIota y
      group
    · ext a b
      change ((veeIota y : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) a b = _
      rw [coe_veeIota_apply]
      change ZMod.castHom (dvd_refl 2) F4 ((1 + single i j (1 : ZMod 2)) a b) = _
      rw [Matrix.add_apply, Matrix.add_apply, map_add]
      congr 1
      · by_cases hab : a = b
        · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
        · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]
      · rw [single_apply, single_apply]
        split_ifs <;> simp
  have hunitri := unitri_of_isPGroup (F := F4) (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num)
    4 hP''2 (Matrix.SpecialLinearGroup.coeMonoidHom.comp P''.subtype) hgen
  have hfwd : ∀ n : Nt, (n : G) ∈ S₀ → g⁻¹ * D n * g ∈ unitriangular 4 F4 := by
    intro n hn
    have hmem : g⁻¹ * D n * g ∈ P'' := ⟨D n, ⟨n, mem_subgroupOf.2 hn, rfl⟩, by
      change g⁻¹ * D n * g⁻¹⁻¹ = g⁻¹ * D n * g
      rw [inv_inv]⟩
    exact hunitri ⟨_, hmem⟩
  set R' : Subgroup Nt := ((unitriangular 4 F4).map (MulAut.conj g).toMonoidHom).comap D
    with hR'def
  have hR'mem : ∀ n : Nt, n ∈ R' ↔ g⁻¹ * D n * g ∈ unitriangular 4 F4 := by
    intro n
    constructor
    · rintro ⟨u, hu, hue⟩
      have h1 : g * u * g⁻¹ = D n := hue
      have h2 : g⁻¹ * D n * g = u := by rw [← h1]; group
      rw [h2]
      exact hu
    · intro hn
      refine ⟨g⁻¹ * D n * g, hn, ?_⟩
      change g * (g⁻¹ * D n * g) * g⁻¹ = D n
      group
  have hU2 : IsPGroup 2 ((unitriangular 4 F4).map (MulAut.conj g).toMonoidHom) := by
    refine (IsPGroup.of_card (n := 12) ?_).map _
    rw [card_unitriangular, Nat.card_eq_fintype_card, F4.card]
    norm_num
  have hkerD : D.ker = W₁.subgroupOf Nt := by
    ext n
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact hDk n
  have hker2 : IsPGroup 2 D.ker := by
    rw [hkerD]
    exact (IsPGroup.of_card hW₁c).comap_subtype
  have hR'2 : IsPGroup 2 R' := hU2.comap_of_ker_isPGroup D hker2
  set R := R'.map Nt.subtype with hRdef
  have hR2 : IsPGroup 2 R := hR'2.map _
  have hS₀R : S₀ ≤ R := fun x hx => ⟨⟨x, hS₀N hx⟩, (hR'mem _).2 (hfwd _ hx), rfl⟩
  have hRN : R ≤ Nt := map_subtype_le _
  have hmul := Subgroup.relIndex_mul_relIndex S₀ R Nt hS₀R hRN
  obtain ⟨k, hk⟩ := hR2.index (S₀.subgroupOf R)
  have h1 : S₀.relIndex R = 2 ^ k := hk
  have hk0 : k = 0 := by
    by_contra hk0
    apply hS₀syl
    rw [← hmul, h1]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hk0) _
  rw [hk0, pow_zero] at h1
  have hRS₀ : R ≤ S₀ := Subgroup.relIndex_eq_one.1 h1
  intro n
  exact ⟨hfwd n, fun hn => hRS₀ ⟨n, (hR'mem n).2 hn, rfl⟩⟩

end Norm

end CFSG.SeitzReduction.LinearPilot
