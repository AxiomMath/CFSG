module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup

variable {X : Type} [Group X]

abbrev CommFourAdj (X : Type) [Group X] (B C : Subgroup X) : Prop :=
  IsKleinFour B ∧ IsKleinFour C ∧ B ≤ centralizer (C : Set X)

theorem commFourAdj_symm {B C : Subgroup X} (h : CommFourAdj X B C) : CommFourAdj X C B :=
  ⟨h.2.1, h.1, le_centralizer_iff.mp h.2.2⟩

theorem reflTransGen_commFourAdj_symm {B C : Subgroup X}
    (h : Relation.ReflTransGen (CommFourAdj X) B C) :
    Relation.ReflTransGen (CommFourAdj X) C B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (commFourAdj_symm hbc) ih

private theorem isKleinFour_map_conj_aux {B : Subgroup X} (hB : IsKleinFour B) (g : X) :
    IsKleinFour (B.map (MulAut.conj g).toMonoidHom) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hB hv, map_one]

private theorem map_conj_le_centralizer_aux {B C : Subgroup X}
    (h : B ≤ centralizer (C : Set X)) (g : X) :
    B.map (MulAut.conj g).toMonoidHom ≤
      centralizer ((C.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨c, hc, rfl⟩
  have hcb : c * b = b * c := mem_centralizer_iff.mp (h hb) c hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * c * g⁻¹ * (g * b * g⁻¹) = g * (c * b) * g⁻¹ := by group
    _ = g * (b * c) * g⁻¹ := by rw [hcb]
    _ = g * b * g⁻¹ * (g * c * g⁻¹) := by group

private theorem map_conj_map_conj_aux (E : Subgroup X) (g h : X) :
    (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private theorem map_conj_one_aux (E : Subgroup X) :
    E.map (MulAut.conj (1 : X)).toMonoidHom = E := by
  ext x
  simp

theorem commFourAdj_map_conj {B C : Subgroup X} (h : CommFourAdj X B C) (g : X) :
    CommFourAdj X (B.map (MulAut.conj g).toMonoidHom) (C.map (MulAut.conj g).toMonoidHom) :=
  ⟨isKleinFour_map_conj_aux h.1 g, isKleinFour_map_conj_aux h.2.1 g,
    map_conj_le_centralizer_aux h.2.2 g⟩

theorem reflTransGen_commFourAdj_map_conj {B C : Subgroup X}
    (h : Relation.ReflTransGen (CommFourAdj X) B C) (g : X) :
    Relation.ReflTransGen (CommFourAdj X) (B.map (MulAut.conj g).toMonoidHom)
      (C.map (MulAut.conj g).toMonoidHom) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (commFourAdj_map_conj hbc g)

private theorem comm_of_mul_self_aux {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1) {a b : X}
    (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have hinv : ∀ x ∈ A, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hA2 x hx)
  calc a * b = (a * b)⁻¹ := (hinv _ (mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv a ha, hinv b hb]

private theorem exists_mem_ne_ne_aux [Finite X] {H : Subgroup X} (h : 2 < Nat.card H)
    (x y : X) : ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hc
  have hsub : (H : Set X) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · by_cases hzy : z = y
      · exact Or.inr hzy
      · exact (hc ⟨z, hz, hzx, hzy⟩).elim
  have hle : Nat.card H ≤ 2 := by
    have e : Nat.card H = (H : Set X).ncard := Nat.card_coe_set_eq (H : Set X)
    rw [e]
    calc (H : Set X).ncard ≤ ({x, y} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y} : Set X).ncard + 1 := Set.ncard_insert_le x {y}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

private theorem mem_centralizer_of_isKleinFour_aux {B : Subgroup X} (hB : IsKleinFour B)
    {w x y : X} (hw : w ∈ B) (hx : x ∈ B) (hw1 : w ≠ 1) (hx1 : x ≠ 1) (hwx : w ≠ x)
    (hyw : w * y = y * w) (hyx : x * y = y * x) : y ∈ centralizer (B : Set X) := by
  rw [mem_centralizer_iff]
  intro b hb
  rcases FooteLit.mem_of_isKleinFour hB hw hx hb hw1 hx1 hwx with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hyw
  · exact hyx
  · calc w * x * y = w * (x * y) := mul_assoc _ _ _
      _ = w * (y * x) := by rw [hyx]
      _ = w * y * x := (mul_assoc _ _ _).symm
      _ = y * w * x := by rw [hyw]
      _ = y * (w * x) := mul_assoc _ _ _

theorem two_lt_card_inf_centralizer [Finite X] {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA8 : 8 ≤ Nat.card A) {f : X} (hfA : f ∈ normalizer (A : Set X)) (hf : f * f = 1) :
    2 < Nat.card ↥(A ⊓ centralizer ({f} : Set X)) := by
  classical
  have hconj : ∀ a ∈ A, f * a * f⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.mp hfA a).mp ha
  let ψ : ↥A →* ↥A := MonoidHom.mk' (fun a => a * ⟨f * a * f⁻¹, hconj a a.2⟩) (fun a b => by
    apply Subtype.ext
    show (a : X) * b * (f * ((a : X) * b) * f⁻¹) =
      (a : X) * (f * a * f⁻¹) * ((b : X) * (f * b * f⁻¹))
    have hc : f * (a : X) * f⁻¹ * b = b * (f * a * f⁻¹) :=
      comm_of_mul_self_aux hA2 (hconj a a.2) b.2
    calc (a : X) * b * (f * ((a : X) * b) * f⁻¹)
        = (a : X) * (b * (f * a * f⁻¹)) * (f * b * f⁻¹) := by group
      _ = (a : X) * (f * a * f⁻¹ * b) * (f * b * f⁻¹) := by rw [hc]
      _ = (a : X) * (f * a * f⁻¹) * ((b : X) * (f * b * f⁻¹)) := by group)
  have hrk : ψ.range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show (a : X) * (f * a * f⁻¹) * (f * ((a : X) * (f * a * f⁻¹)) * f⁻¹) = 1
    have ha : (a : X) * a = 1 := hA2 a a.2
    have ha' : f * (a : X) * f⁻¹ * (f * a * f⁻¹) = 1 := hA2 _ (hconj a a.2)
    calc (a : X) * (f * a * f⁻¹) * (f * ((a : X) * (f * a * f⁻¹)) * f⁻¹)
        = (a : X) * (f * a * f⁻¹ * (f * a * f⁻¹)) * (f * f * a * (f * f)⁻¹) := by group
      _ = 1 := by simp only [ha', hf, inv_one, mul_one, one_mul, ha]
  have hcard : Nat.card ↥A = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have h1 : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrk
  have h2 : Nat.card ψ.ker ≤ Nat.card ↥(A ⊓ centralizer ({f} : Set X)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥A) : X), (x : ↥A).2, ?_⟩) fun x y hxy => ?_
    · have h0 : ((x : ↥A) : X) * (f * (x : ↥A) * f⁻¹) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      have hxx : ((x : ↥A) : X) * (x : ↥A) = 1 := hA2 _ (x : ↥A).2
      have he : f * ((x : ↥A) : X) * f⁻¹ = (x : ↥A) := by
        calc f * ((x : ↥A) : X) * f⁻¹
            = ((x : ↥A) : X) * (((x : ↥A) : X) * (f * (x : ↥A) * f⁻¹)) := by
              rw [← mul_assoc, hxx, one_mul]
          _ = (x : ↥A) := by rw [h0, mul_one]
      refine mem_centralizer_singleton_iff.mpr ?_
      calc ((x : ↥A) : X) * f = f * ((x : ↥A) : X) * f⁻¹ * f := by rw [he]
        _ = f * (x : ↥A) := by group
    · have h' := Subtype.ext_iff.mp hxy
      exact Subtype.ext (Subtype.ext h')
  by_contra hlt
  have hle : Nat.card ↥A ≤ 4 := by
    rw [hcard]
    calc Nat.card ψ.range * Nat.card ψ.ker ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 := by norm_num
  omega

private theorem exists_mem_centralizer_ne_aux [Finite X] {A : Subgroup X}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A) {f : X}
    (hfA : f ∈ normalizer (A : Set X)) (hf : f * f = 1) (c : X) :
    ∃ d ∈ A, d * f = f * d ∧ d ≠ 1 ∧ d ≠ c := by
  obtain ⟨d, hd, hd1, hdc⟩ := exists_mem_ne_ne_aux (two_lt_card_inf_centralizer hA2 hA8 hfA hf) 1 c
  exact ⟨d, hd.1, mem_centralizer_singleton_iff.mp hd.2, hd1, hdc⟩

theorem exists_reflTransGen_le_of_le_normalizer [Finite X] {A : Subgroup X}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A) {F : Subgroup X} (hF : IsKleinFour F)
    (hFA : F ≤ normalizer (A : Set X)) :
    ∃ E : Subgroup X, E ≤ A ∧ IsKleinFour E ∧ Relation.ReflTransGen (CommFourAdj X) F E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [hF.card_four]; norm_num)
  have hFsq : ∀ x ∈ F, x * x = 1 := fun x hx => by
    rw [← sq]
    exact FooteLit.sq_eq_one_of_isKleinFour hF hx
  have hF4 : 2 < Nat.card F := by rw [hF.card_four]; norm_num
  have hAeven : Even (Nat.card A) := by
    obtain ⟨a, haA, ha1, -⟩ := exists_mem_ne_ne_aux (H := A) (by omega) 1 1
    have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hA2 a haA) ha1
    exact even_iff_two_dvd.mpr (ha2 ▸ A.orderOf_dvd_natCard haA)
  obtain ⟨c, hcA, hc2, hcF⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer hF2 hFA hAeven
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc2; norm_num at hc2
  have hcsq : c ^ 2 = 1 := by rw [← hc2]; exact pow_orderOf_eq_one c
  have hcC : c ∈ centralizer (F : Set X) := mem_centralizer_iff.mpr hcF
  by_cases hd : ∃ d ∈ A, d ≠ 1 ∧ d ≠ c ∧ ∀ p ∈ F, p * d = d * p
  ·
    obtain ⟨d, hdA, hd1, hdc, hdF⟩ := hd
    obtain ⟨E, hE, hEK, -, -⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le
      (A ⊓ centralizer (F : Set X)) c d ⟨hc1, hcsq⟩ ⟨hd1, by rw [sq]; exact hA2 d hdA⟩
      (fun h => hdc h.symm) (comm_of_mul_self_aux hA2 hcA hdA) ⟨hcA, hcC⟩
      ⟨hdA, mem_centralizer_iff.mpr hdF⟩
    have hFE : CommFourAdj X F E := ⟨hF, hEK, le_centralizer_iff.mp (hE.trans inf_le_right)⟩
    exact ⟨E, hE.trans inf_le_left, hEK, Relation.ReflTransGen.single hFE⟩
  have hcF' : c ∉ F := by
    intro hcF'
    obtain ⟨f, hfF, hf1, hfc⟩ := exists_mem_ne_ne_aux hF4 1 c
    obtain ⟨d, hdA, hdf, hd1, hdc⟩ :=
      exists_mem_centralizer_ne_aux hA2 hA8 (hFA hfF) (hFsq f hfF) c
    refine hd ⟨d, hdA, hd1, hdc, fun p hp => ?_⟩
    have hpC := mem_centralizer_of_isKleinFour_aux hF hcF' hfF hc1 hf1 (fun h => hfc h.symm)
      (comm_of_mul_self_aux hA2 hcA hdA) hdf.symm
    exact mem_centralizer_iff.mp hpC p hp
  obtain ⟨f, hfF, hf1, -⟩ := exists_mem_ne_ne_aux hF4 1 1
  have hfc : f ≠ c := fun h => hcF' (h ▸ hfF)
  have hfC : f ∈ centralizer (F : Set X) := mem_centralizer_iff.mpr fun p hp =>
    comm_of_mul_self_aux hFsq hp hfF
  obtain ⟨B, hBC, hB, hfB, hcB⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le
    (centralizer (F : Set X)) f c ⟨hf1, by rw [sq]; exact hFsq f hfF⟩ ⟨hc1, hcsq⟩ hfc
    (hcF f hfF) hfC hcC
  obtain ⟨d, hdA, hdf, hd1, hdc⟩ :=
    exists_mem_centralizer_ne_aux hA2 hA8 (hFA hfF) (hFsq f hfF) c
  have hcd : c * d = d * c := comm_of_mul_self_aux hA2 hcA hdA
  have hcBC : c ∈ centralizer (B : Set X) := mem_centralizer_of_isKleinFour_aux hB hfB hcB hf1
    hc1 hfc (hcF f hfF) rfl
  have hdBC : d ∈ centralizer (B : Set X) := mem_centralizer_of_isKleinFour_aux hB hfB hcB hf1
    hc1 hfc hdf.symm hcd
  obtain ⟨E, hE, hEK, -, -⟩ := GorensteinWalter.exists_kleinFour_of_commuting_involutions_le
    (A ⊓ centralizer (B : Set X)) c d ⟨hc1, hcsq⟩ ⟨hd1, by rw [sq]; exact hA2 d hdA⟩
    (fun h => hdc h.symm) hcd ⟨hcA, hcBC⟩ ⟨hdA, hdBC⟩
  have hFB : CommFourAdj X F B := ⟨hF, hB, le_centralizer_iff.mp hBC⟩
  have hBE : CommFourAdj X B E := ⟨hB, hEK, le_centralizer_iff.mp (hE.trans inf_le_right)⟩
  exact ⟨E, hE.trans inf_le_left, hEK, (Relation.ReflTransGen.single hFB).tail hBE⟩

theorem reflTransGen_commFourAdj_of_le_normalizer [Finite X] {A : Subgroup X}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A) {E F : Subgroup X}
    (hE : IsKleinFour E) (hEA : E ≤ normalizer (A : Set X)) (hF : IsKleinFour F)
    (hFA : F ≤ normalizer (A : Set X)) : Relation.ReflTransGen (CommFourAdj X) E F := by
  obtain ⟨E₁, hE₁A, hE₁, h₁⟩ := exists_reflTransGen_le_of_le_normalizer hA2 hA8 hE hEA
  obtain ⟨F₁, hF₁A, hF₁, h₂⟩ := exists_reflTransGen_le_of_le_normalizer hA2 hA8 hF hFA
  have h₃ : CommFourAdj X E₁ F₁ := ⟨hE₁, hF₁, fun x hx => mem_centralizer_iff.mpr fun y hy =>
    comm_of_mul_self_aux hA2 (hF₁A hy) (hE₁A hx)⟩
  exact (h₁.tail h₃).trans (reflTransGen_commFourAdj_symm h₂)

theorem reflTransGen_commFourAdj_of_normal_elemAbelian [Finite X] {S A : Subgroup X}
    (hSA : S ≤ normalizer (A : Set X)) (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A)
    {E F : Subgroup X} (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj X) E F :=
  reflTransGen_commFourAdj_of_le_normalizer hA2 hA8 hE (hES.trans hSA) hF (hFS.trans hSA)

theorem not_exists_elemAbelian_of_not_reflTransGen [Finite X] {S E F : Subgroup X}
    (hE : IsKleinFour E) (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S)
    (h : ¬ Relation.ReflTransGen (CommFourAdj X) E F) :
    ¬ ∃ A : Subgroup X, S ≤ normalizer (A : Set X) ∧ (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A :=
  fun ⟨_, hSA, hA2, hA8⟩ =>
    h (reflTransGen_commFourAdj_of_normal_elemAbelian hSA hA2 hA8 hE hES hF hFS)

private theorem exists_map_conj_le_aux [Finite X] {E : Subgroup X} (hE : IsPGroup 2 E)
    (S : Sylow 2 X) : ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P S
  have h : ((g • P : Sylow 2 X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := rfl
  exact ⟨g, by rw [← hg, h]; exact Subgroup.map_mono hP⟩

theorem not_isTwoDisconnected_of_gamma_eq_top [Finite X] (S : Sylow 2 X)
    (hconn : ∀ E F : Subgroup X, IsKleinFour E → E ≤ S → IsKleinFour F → F ≤ S →
      Relation.ReflTransGen (CommFourAdj X) E F)
    (hΓ : CFSG.Open.properTwoGenCoreGamma (S : Subgroup X) 2 = ⊤) :
    ¬ FooteLit.IsTwoDisconnected X := by
  rintro ⟨B, C, hB, hC, hBC⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 2) (by rw [hB.card_four]; norm_num)
  obtain ⟨g₀, hg₀⟩ := exists_map_conj_le_aux hB2 S
  set E₀ := B.map (MulAut.conj g₀).toMonoidHom
  have hE₀ : IsKleinFour E₀ := isKleinFour_map_conj_aux hB g₀
  let H : Subgroup X :=
    { carrier := {g | Relation.ReflTransGen (CommFourAdj X) E₀
        (E₀.map (MulAut.conj g).toMonoidHom)}
      one_mem' := by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj (1 : X)).toMonoidHom)
        exact (congrArg (Relation.ReflTransGen (CommFourAdj X) E₀) (map_conj_one_aux E₀)).mpr
          Relation.ReflTransGen.refl
      mul_mem' := fun {g h} hg hh => by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj (g * h)).toMonoidHom)
        rw [← map_conj_map_conj_aux E₀ g h]
        exact hg.trans (reflTransGen_commFourAdj_map_conj hh g)
      inv_mem' := fun {g} hg => by
        show Relation.ReflTransGen _ E₀ (E₀.map (MulAut.conj g⁻¹).toMonoidHom)
        have h := reflTransGen_commFourAdj_map_conj hg g⁻¹
        rw [map_conj_map_conj_aux E₀ g⁻¹ g, inv_mul_cancel, map_conj_one_aux E₀] at h
        exact reflTransGen_commFourAdj_symm h }
  have hΓH : CFSG.Open.properTwoGenCoreGamma (S : Subgroup X) 2 ≤ H := by
    refine (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ _ 2).mpr fun Q hQS hQ g hg => ?_
    obtain ⟨E₁, hE₁Q, hE₁e, hE₁c⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hQ
    have hE₁ : IsKleinFour E₁ :=
      FooteLit.isKleinFour_of_card_eq_four (by rw [hE₁c]; norm_num) hE₁e.2
    have hmap : E₁.map (MulAut.conj g).toMonoidHom ≤ Q := by
      rw [← mem_normalizer_iff_map_conj_eq.mp hg]
      exact Subgroup.map_mono hE₁Q
    have h1 := hconn E₀ E₁ hE₀ hg₀ hE₁ (hE₁Q.trans hQS)
    have h2 := hconn _ E₀ (isKleinFour_map_conj_aux hE₁ g) (hmap.trans hQS) hE₀ hg₀
    exact reflTransGen_commFourAdj_symm ((reflTransGen_commFourAdj_map_conj h1 g).trans h2)
  have hH : H = ⊤ := top_le_iff.mp (by rw [← hΓ]; exact hΓH)
  have hjoin : ∀ D : Subgroup X, IsKleinFour D → Relation.ReflTransGen (CommFourAdj X) D E₀ := by
    intro D hD
    have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 2) (by rw [hD.card_four]; norm_num)
    obtain ⟨x, hx⟩ := exists_map_conj_le_aux hD2 S
    have h1 := hconn _ E₀ (isKleinFour_map_conj_aux hD x) hx hE₀ hg₀
    have h2 := reflTransGen_commFourAdj_map_conj h1 x⁻¹
    rw [map_conj_map_conj_aux D x⁻¹ x, inv_mul_cancel, map_conj_one_aux D] at h2
    have h3 : Relation.ReflTransGen (CommFourAdj X) E₀
        (E₀.map (MulAut.conj x⁻¹).toMonoidHom) := by
      have hx' : x⁻¹ ∈ H := by rw [hH]; exact mem_top _
      exact hx'
    exact h2.trans (reflTransGen_commFourAdj_symm h3)
  exact hBC ((hjoin B hB).trans (reflTransGen_commFourAdj_symm (hjoin C hC)))

theorem exists_not_reflTransGen_of_isTwoDisconnected [Finite X] (S : Sylow 2 X)
    (hΓ : CFSG.Open.properTwoGenCoreGamma (S : Subgroup X) 2 = ⊤)
    (h : FooteLit.IsTwoDisconnected X) :
    ∃ E F : Subgroup X, IsKleinFour E ∧ E ≤ S ∧ IsKleinFour F ∧ F ≤ S ∧
      ¬ Relation.ReflTransGen (CommFourAdj X) E F := by
  by_contra hc
  refine not_isTwoDisconnected_of_gamma_eq_top S (fun E F hE hES hF hFS => ?_) hΓ h
  by_contra h'
  exact hc ⟨E, F, hE, hES, hF, hFS, h'⟩

end CFSG.ComponentClassification.Sol76.Sig
