module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcTorusAct

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (baseChangeGL_mem_torusGroup)
open CFSG.HardMathSupport.Curtis.UnitaryLevi (What Z0 monoι monoι_torusN Z0_comm Z0_sq Z0_conj_What
  What_ker_le_Z0 exists_lift Z0_le_range_torusN)

section Abstract

theorem exists_coboundary {G : Type*} [Group G] (Z Q : Subgroup G) [Finite Q]
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hodd : Odd (Nat.card Q)) (hZn : ∀ g ∈ Q, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (c : G → G) (hcZ : ∀ g ∈ Q, c g ∈ Z)
    (hc : ∀ g ∈ Q, ∀ h ∈ Q, c (g * h) = c g * (g * c h * g⁻¹)) :
    ∃ P ∈ Z, ∀ g ∈ Q, c g = P * (g * P * g⁻¹)⁻¹ := by
  classical
  let _ : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hZc a.1 a.2 b.1 b.2) }
  let _ := Fintype.ofFinite Q
  let φ : Q → Z := fun h => ⟨c h, hcZ h h.2⟩
  let cj : Q → Z →* Z := fun g => MonoidHom.mk' (fun z => ⟨(g : G) * z * (g : G)⁻¹, hZn g g.2 z z.2⟩)
    (fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group))
  refine ⟨(∏ h : Q, φ h : Z), (∏ h : Q, φ h : Z).2, fun g hg => ?_⟩
  have h1 : ∏ h : Q, φ (⟨g, hg⟩ * h) = ∏ h : Q, φ h :=
    Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : Q)) _ _ (fun h => rfl)
  have h2 : ∀ h : Q, φ (⟨g, hg⟩ * h) = φ ⟨g, hg⟩ * cj ⟨g, hg⟩ (φ h) :=
    fun h => Subtype.ext (hc g hg h h.2)
  have h3 : (∏ h : Q, φ h) = φ ⟨g, hg⟩ ^ Fintype.card Q * cj ⟨g, hg⟩ (∏ h : Q, φ h) := by
    calc (∏ h : Q, φ h) = ∏ h : Q, φ (⟨g, hg⟩ * h) := h1.symm
      _ = ∏ h : Q, (φ ⟨g, hg⟩ * cj ⟨g, hg⟩ (φ h)) := Finset.prod_congr rfl fun h _ => h2 h
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_prod]
  have hsq : φ ⟨g, hg⟩ ^ 2 = 1 := Subtype.ext (hZ2 _ (hcZ g hg))
  have h4 : φ ⟨g, hg⟩ ^ Fintype.card Q = φ ⟨g, hg⟩ := by
    obtain ⟨k, hk⟩ := hodd
    rw [Fintype.card_eq_nat_card, hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  rw [h4] at h3
  have h5 := eq_mul_inv_of_mul_eq h3.symm
  exact congrArg Subtype.val h5

theorem conj_fixed_aux {G : Type*} [Group G] (t u y P γ : G) (ht : t * u⁻¹ = P)
    (hcomm : t * P = P * t) (hγ : γ = P * (y * P * y⁻¹)⁻¹) :
    u * (γ * y) * u⁻¹ = t * y * t⁻¹ := by
  have hu : u = P⁻¹ * t := by rw [← ht]; group
  have h1 : P⁻¹ * t * P = t := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
  have h2 : P⁻¹ * t⁻¹ * P = t⁻¹ := by
    calc P⁻¹ * t⁻¹ * P = (P⁻¹ * t * P)⁻¹ := by group
      _ = t⁻¹ := by rw [h1]
  subst hu hγ
  calc P⁻¹ * t * (P * (y * P * y⁻¹)⁻¹ * y) * (P⁻¹ * t)⁻¹
      = (P⁻¹ * t * P) * y * (P⁻¹ * t⁻¹ * P) := by group
    _ = t * y * t⁻¹ := by rw [h1, h2]

end Abstract

section Main

variable (τ : Tag) (F L : Type) [Field F] [Field L] [Algebra F L]

@[expose] def tiL : ↥(monomialSub τ F) →* ModGL τ L :=
  (baseChangeGL (τ := τ) (algebraMap F L)).comp (monoι τ F)

variable {τ F L}

theorem tiL_mem_monomialSubgroup (g : ↥(monomialSub τ F)) :
    tiL τ F L g ∈ monomialSubgroup τ L :=
  baseChangeGL_mem_monomialSubgroup _ g.2

theorem canonicalRep_baseChange_eq {R S : Type} [Field R] [Field S] (f : R →+* S)
    (w : WeylGroup τ) :
    baseChangeGL f (canonicalRep (coxeterSystem τ) R w) = canonicalRep (coxeterSystem τ) S w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => baseChangeGL_weylElt_one f i)

theorem tiL_frobenius [Finite F] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    (g : ↥(monomialSub τ F)) :
    Units.map (entrywiseHom Fr) (tiL τ F L g) = tiL τ F L g := by
  have hcomp : Fr.comp (algebraMap F L) = algebraMap F L := by
    refine RingHom.ext fun c => ?_
    have := Fintype.ofFinite F
    rw [RingHom.comp_apply, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [entrywise_eq_baseChangeGL]
  show baseChangeGL Fr (baseChangeGL (algebraMap F L) (monoι τ F g)) = _
  rw [baseChangeGL_baseChangeGL, hcomp]
  rfl

theorem exists_What_canonicalRep (w : WeylGroup τ) :
    ∃ a ∈ What τ F, monoι τ F a = canonicalRep (coxeterSystem τ) F w ∧
      monomialSubHom (τ := τ) (K := F) a = w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  have hmono : monoι τ F ((ω.map (weylRep τ F)).prod) =
      canonicalRep (coxeterSystem τ) F ((coxeterSystem τ).wordProd ω) := by
    rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => UnitaryLevi.monoι_weylRep τ F i)
  refine ⟨(ω.map (weylRep τ F)).prod, list_prod_mem fun x hx => ?_, hmono, ?_⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact UnitaryLevi.weylRep_mem_What τ F i
  · have h : MapsRootLines (monoι τ F ((ω.map (weylRep τ F)).prod))
        ((coxeterSystem τ).wordProd ω) := by
      rw [hmono]
      exact mapsRootLines_canonicalRep _
    exact weylQuotientHom_eq h

theorem mapsRootLines_tiL (g : ↥(monomialSub τ F)) :
    MapsRootLines (tiL τ F L g) (monomialSubHom (τ := τ) (K := F) g) := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2
  have hgk' : monoι τ F g = k * canonicalRep (coxeterSystem τ) F w := hgk
  have h1 : MapsRootLines (monoι τ F g) w := by
    rw [hgk']
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have h2 : monomialSubHom (τ := τ) (K := F) g = w := weylQuotientHom_eq h1
  rw [h2]
  show MapsRootLines (baseChangeGL (algebraMap F L) (monoι τ F g)) w
  rw [hgk', map_mul, canonicalRep_baseChange_eq]
  simpa using (mapsRootLines_of_mem_torusGroup (baseChangeGL_mem_torusGroup _ hk)).mul
    (mapsRootLines_canonicalRep (R := L) w)

theorem tiL_Z0_mem_torusGroup [Finite F] {z : ↥(monomialSub τ F)} (hz : z ∈ Z0 τ F) :
    tiL τ F L z ∈ torusGroup τ L := by
  obtain ⟨t, rfl⟩ := Z0_le_range_torusN τ hz
  show baseChangeGL (algebraMap F L) (monoι τ F (UnitaryLevi.torusN τ F t)) ∈ _
  rw [monoι_torusN]
  exact baseChangeGL_mem_torusGroup _ (torusCoordHom τ F t).2

theorem exists_nfix_lift [Finite F] [IsAlgClosed L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card F) (w : WeylGroup τ) (Q : Subgroup (WeylGroup τ))
    (hQ : IsPGroup 3 Q) (hQw : Q ≤ Subgroup.centralizer ({w} : Set (WeylGroup τ))) :
    ∃ C : Subgroup (NFix (canonicalRep (coxeterSystem τ) L w) Fr),
      (∀ x ∈ C, ∀ y ∈ C, NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr x =
        NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr y → x = y) ∧
      (∀ q ∈ Q, ∃ c ∈ C, NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr c = q) ∧
      ∀ c ∈ C, NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr c ∈ Q := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨Qh, hQhW, hinj, hsurj, hmem⟩ := exists_lift τ F Q hQ
  obtain ⟨a, haW, hmono, haw⟩ := exists_What_canonicalRep (τ := τ) (F := F) w
  have hna : canonicalRep (coxeterSystem τ) L w = tiL τ F L a := by
    show _ = baseChangeGL (algebraMap F L) (monoι τ F a)
    rw [hmono, canonicalRep_baseChange_eq]
  obtain ⟨c, hc⟩ : ∃ c : ↥(monomialSub τ F) → ↥(monomialSub τ F),
      ∀ g, c g = a * g * a⁻¹ * g⁻¹ := ⟨_, fun _ => rfl⟩
  have hcZ : ∀ g ∈ Qh, c g ∈ Z0 τ F := by
    intro g hg
    refine What_ker_le_Z0 τ F ?_ ?_
    · rw [hc]
      exact mul_mem (mul_mem (mul_mem haW (hQhW hg)) (inv_mem haW)) (inv_mem (hQhW hg))
    · have hu : monomialSubHom (τ := τ) (K := F) g ∈ Q := hmem g hg
      have hcomm : w * monomialSubHom (τ := τ) (K := F) g =
          monomialSubHom (τ := τ) (K := F) g * w :=
        Subgroup.mem_centralizer_iff.1 (hQw hu) w (Set.mem_singleton w)
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, haw, hcomm, mul_inv_cancel_right,
        mul_inv_cancel]
  have hcoc : ∀ g ∈ Qh, ∀ h ∈ Qh, c (g * h) = c g * (g * c h * g⁻¹) := fun g _ h _ => by
    simp only [hc]
    group
  have hodd : Odd (Nat.card Qh) := by
    let f : Qh →* Q := ((monomialSubHom (τ := τ) (K := F)).comp Qh.subtype).codRestrict Q
      (fun x => hmem x x.2)
    have hf : Function.Injective f := fun x y h =>
      Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val h))
    obtain ⟨k, hk⟩ := (IsPGroup.of_injective hQ f hf).exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨P, hPZ, hPc⟩ := exists_coboundary (Z0 τ F) Qh (fun a ha b hb => Z0_comm τ F ha hb)
    (fun z hz => Z0_sq τ F hz) hodd (fun g hg z hz => Z0_conj_What τ F (hQhW hg) hz) c hcZ hcoc
  have hP' : tiL τ F L P ∈ torusGroup τ L := tiL_Z0_mem_torusGroup hPZ
  obtain ⟨t, ht, htP⟩ := exists_mul_negPhi_inv_eq_gen Fr w hq hFr hP'
  have hTcomm : t * tiL τ F L P = tiL τ F L P * t := torusGroup_mul_comm ht hP'
  have key : ∀ g ∈ Qh,
      t * tiL τ F L g * t⁻¹ ∈ NFix (canonicalRep (coxeterSystem τ) L w) Fr := by
    intro g hg
    have htm : t ∈ monomialSubgroup τ L := torusGroup_le_monomialSubgroup' ht
    rw [mem_NFix]
    refine ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htm (tiL_mem_monomialSubgroup g))
        (Subgroup.inv_mem _ htm)
    · have hy : negPhi Fr (canonicalRep (coxeterSystem τ) L w) (tiL τ F L g) =
          tiL τ F L (c g) * tiL τ F L g := by
        rw [negPhi_apply, tiL_frobenius Fr hFr g, hna]
        simp only [hc, map_mul, map_inv]
        group
      rw [map_mul, map_mul, map_inv, hy]
      refine conj_fixed_aux t _ (tiL τ F L g) (tiL τ F L P) (tiL τ F L (c g)) htP hTcomm ?_
      rw [hPc g hg]
      simp only [map_mul, map_inv]
  have hW : ∀ g ∈ Qh, MapsRootLines (t * tiL τ F L g * t⁻¹)
      (monomialSubHom (τ := τ) (K := F) g) := fun g _ => by
    simpa using ((mapsRootLines_of_mem_torusGroup ht).mul (mapsRootLines_tiL (L := L) g)).mul
      (mapsRootLines_of_mem_torusGroup ht).inv
  let θ : ↥(monomialSub τ F) →* ModGL τ L :=
    (MulAut.conj t).toMonoidHom.comp (tiL τ F L)
  have hθ : ∀ g, θ g = t * tiL τ F L g * t⁻¹ := fun g => rfl
  refine ⟨(Qh.map θ).subgroupOf (NFix (canonicalRep (coxeterSystem τ) L w) Fr), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨g, hg, hgx⟩ := hx
    obtain ⟨g', hg', hgy⟩ := hy
    have e1 : NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr x =
        monomialSubHom (τ := τ) (K := F) g :=
      NFixToWeyl_eq (by rw [← hgx, hθ]; exact hW g hg)
    have e2 : NFixToWeyl (canonicalRep (coxeterSystem τ) L w) Fr y =
        monomialSubHom (τ := τ) (K := F) g' :=
      NFixToWeyl_eq (by rw [← hgy, hθ]; exact hW g' hg')
    have hgg : g = g' := hinj g hg g' hg' (by rw [← e1, ← e2, hxy])
    exact Subtype.ext (by rw [← hgx, ← hgy, hgg])
  · intro q hq'
    obtain ⟨g, hg, rfl⟩ := hsurj q hq'
    refine ⟨⟨θ g, key g hg⟩, ?_, NFixToWeyl_eq (hW g hg)⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨g, hg, rfl⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    rw [NFixToWeyl_eq (w := monomialSubHom (τ := τ) (K := F) g) (by rw [← hgx, hθ]; exact hW g hg)]
    exact hmem g hg

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
