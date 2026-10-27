module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false

variable {τ : Tag} {k : Type} [Field k]

section Lin

@[expose] def subLin {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (y : Fin m → ZMod 3) :
    Fin τ.rank → ZMod 3 :=
  ∑ i, y i • e i

@[expose] def liftL {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (b : List ℕ) : List ℕ :=
  List.ofFn fun i => (subLin e (listVec m b) i).val

theorem subLin_add {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (y z : Fin m → ZMod 3) :
    subLin e (y + z) = subLin e y + subLin e z := by
  simp only [subLin, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem subLin_zero {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) : subLin e 0 = 0 := by
  simp [subLin]

theorem length_liftL {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (b : List ℕ) :
    (liftL e b).length = τ.rank := by
  simp [liftL]

theorem lt_of_mem_liftL {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (b : List ℕ) :
    ∀ x ∈ liftL e b, x < 3 := by
  intro x hx
  rw [liftL, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ZMod.val_lt _

theorem listVec_liftL {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (b : List ℕ) :
    listVec τ.rank (liftL e b) = subLin e (listVec m b) := by
  funext i
  rw [listVec, liftL, List.getD_eq_getElem _ _ (by simp)]
  simp

theorem subLin_single {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3) (i : Fin m) :
    subLin e (Pi.single i 1) = e i := by
  rw [subLin, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem length_stdBasis' (m : ℕ) : (Native.stdBasis m).length = m := by
  simp [Native.stdBasis]

theorem listVec_stdBasis' (m : ℕ) (j : Fin (Native.stdBasis m).length) :
    listVec m ((Native.stdBasis m).get j) =
      Pi.single (⟨j.val, by simpa [length_stdBasis'] using j.2⟩ : Fin m) 1 := by
  funext i
  have hget : (Native.stdBasis m).get j =
      (List.range m).map fun l => if l = j.val then 1 else 0 := by
    rw [List.get_eq_getElem]
    simp [Native.stdBasis]
  rw [hget, listVec, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> simp

end Lin

section DV

theorem dV_nsmul {ω : kˣ} (hω : ω ^ 3 = 1) (n : ℕ) (x : Fin τ.rank → ZMod 3) :
    dV ω (n • x) = dV ω x ^ n := by
  rw [← dVHom_ofAdd hω, ofAdd_nsmul, map_pow, dVHom_ofAdd]

private theorem dV_pow_three_subS {ω : kˣ} (hω : ω ^ 3 = 1) (x : Fin τ.rank → ZMod 3) :
    dV ω x ^ 3 = 1 := by
  rw [← dV_nsmul hω]
  have h : (3 • x) = 0 := by
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    have : (3 : ZMod 3) = 0 := rfl
    rw [Nat.cast_ofNat, this, zero_mul]
  rw [h, dV_zero]

theorem dV_list_sum {ω : kˣ} (hω : ω ^ 3 = 1) (l : List (Fin τ.rank → ZMod 3)) :
    dV ω l.sum = (l.map (dV ω)).prod := by
  induction l with
  | nil => simp [dV_zero]
  | cons x l ih => rw [List.sum_cons, dV_add hω, ih, List.map_cons, List.prod_cons]

theorem dV_subLin {ω : kˣ} (hω : ω ^ 3 = 1) {m : ℕ} (e : Fin m → Fin τ.rank → ZMod 3)
    (a : Fin m → ZMod 3) :
    dV ω (subLin e a) = ((List.finRange m).map fun i => dV ω (e i) ^ (a i).val).prod := by
  have h1 : subLin e a = ((List.finRange m).map fun i => (a i).val • e i).sum := by
    rw [subLin, Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h1, dV_list_sum hω, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  exact dV_nsmul hω _ _

end DV

section FamCent

variable {G : Subgroup (ModGL τ k)} {ω : kˣ}

@[expose] noncomputable def famCentS (ω : kˣ) (G : Subgroup (ModGL τ k)) (kb : List (List ℕ)) :
    Subgroup G :=
  ⨅ j : Fin kb.length,
    (Subgroup.centralizer {dV (τ := τ) ω (listVec τ.rank (kb.get j))}).subgroupOf G

theorem mem_famCentS {kb : List (List ℕ)} {g : G} :
    g ∈ famCentS ω G kb ↔ ∀ j : Fin kb.length, (g : ModGL τ k) * dV ω (listVec τ.rank (kb.get j)) =
      dV ω (listVec τ.rank (kb.get j)) * g := by
  rw [famCentS, Subgroup.mem_iInf]
  exact forall_congr' fun j => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]

end FamCent

section Leaf


variable {G : Subgroup (ModGL τ k)} [Finite G] {ω : kˣ}

theorem mem_familyCentralizer_of_mem_famCentS (hGC : G ≤ adjointGroup τ k)
    {kb : List (List ℕ)} {g : G} (hg : g ∈ famCentS ω G kb) :
    (g : ModGL τ k) ∈ familyCentralizer τ k (famV (τ := τ) ω kb) := by
  rw [mem_familyCentralizer]
  refine ⟨hGC g.2, fun j => ?_⟩
  have h1 := (mem_famCentS.1 hg) j
  change dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ = g
  rw [← h1, mul_assoc, mul_inv_cancel, mul_one]

theorem gLAPPrimeCoreOf_leafS (hGC : G ≤ adjointGroup τ k) {kb : List (List ℕ)}
    (hX3 : ∀ g ∈ G, g ∈ torusGroup τ k → g ^ 3 = 1)
    (hcase : (familyKernel (famV (τ := τ) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        (∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α) ∧
        (∀ g ∈ G, g ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} → g ^ 3 ∈ rootSpan τ k {α, -α}) ∧
        ∀ N : Subgroup G, (∀ n ∈ N, (n : ModGL τ k) ∈ rootSpan τ k {α, -α}) →
          (∀ g : G, (g : ModGL τ k) ∈ rootSpan τ k {α, -α} → ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
          Nat.Coprime 3 (Nat.card N) → N = ⊥) :
    GLAPPrimeCoreOf 3 (famCentS ω G kb) = ⊥ := by
  set C := famCentS ω G kb
  set O := GLAPPrimeCoreOf 3 C
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_gLAPPrimeCoreOf' Nat.prime_three C
  have hord : ∀ o ∈ O, Nat.Coprime 3 (orderOf (o : ModGL τ k)) := by
    intro o ho
    have h1 : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    have h2 : orderOf (o : ModGL τ k) = orderOf (⟨o, ho⟩ : O) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rw [h2]
    exact hcop.coprime_dvd_right h1
  have hfac := fun {o : G} (ho : o ∈ O) => familyCentralizer_le_mul τ k (famV (τ := τ) ω kb)
    (mem_familyCentralizer_of_mem_famCentS hGC (gLAPPrimeCoreOf_le_self' C ho))
  rcases hcase with ⟨hK, hW⟩ | ⟨α, hα, hK, hW, hX4, hX5⟩
  · refine eq_bot_iff.2 fun o ho => ?_
    obtain ⟨w, hw, m, hm, he⟩ := hfac ho
    rw [hW w hw, canonicalRep_one, mul_one] at he
    have hmT : m ∈ torusGroup τ k := by
      have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
      rw [hK] at hm'
      have hbot : rootSpan τ k (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by
        simp [rootSpan]
      rwa [hbot, sup_bot_eq] at hm'
    have h3 : (o : ModGL τ k) ^ 3 = 1 := hX3 _ o.2 (he ▸ hmT)
    have h1 := mem_of_pow_three_mem (hord o ho) (P := ⊥) (by rw [h3]; exact one_mem _)
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  · set L := rootSpan τ k {α, -α}
    have hOL : ∀ o ∈ O, (o : ModGL τ k) ∈ L := by
      intro o ho
      obtain ⟨w, hw, m, hm, he⟩ := hfac ho
      have hmM : m ∈ torusGroup τ k ⊔ L := by
        have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
        rwa [hK] at hm'
      have hoM : (o : ModGL τ k) ∈ torusGroup τ k ⊔ L := by
        rw [he]
        rcases hW w hw with rfl | rfl
        · rwa [canonicalRep_one, mul_one]
        · exact mul_mem hmM (canonicalRep_rootReflection_mem hα)
      exact mem_of_pow_three_mem (hord o ho) (hX4 _ o.2 hoM)
    have hLC : ∀ g : G, (g : ModGL τ k) ∈ L → g ∈ C := by
      intro g hg
      have hgF : (g : ModGL τ k) ∈ familyCentralizer τ k (famV (τ := τ) ω kb) := by
        refine familyGroup_le_familyCentralizer (K := k) _ ?_
        change (g : ModGL τ k) ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb))
        rw [hK]
        exact le_sup_right (a := torusGroup τ k) hg
      refine mem_famCentS.2 fun j => ?_
      have h1 := (mem_familyCentralizer.1 hgF).2 j
      have h2 : dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ =
        (g : ModGL τ k) := h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    exact hX5 O hOL (fun g hg n hn => gLAPPrimeCoreOf_conj_mem' g (hLC g hg) n hn) hcop

end Leaf

section Assembly

variable {G : Subgroup (ModGL τ k)} [Finite G] {ω : kˣ}

@[expose] noncomputable def genS {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (i : Fin m) : G :=
  ⟨dV ω (e i), he i⟩

theorem dV_subLin_mem (hω : ω ^ 3 = 1) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (a : Fin m → ZMod 3) : dV ω (subLin e a) ∈ G := by
  rw [dV_subLin hω]
  refine Subgroup.list_prod_mem (K := G) fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact pow_mem (he i) _

@[expose] noncomputable def dS (hω : ω ^ 3 = 1) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (a : Fin m → ZMod 3) : G :=
  ⟨dV ω (subLin e a), dV_subLin_mem hω he a⟩

theorem genS_comm (hω : ω ^ 3 = 1) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (i j : Fin m) : Commute (genS he i) (genS he j) := by
  refine Subtype.ext ?_
  change dV ω (e i) * dV ω (e j) = dV ω (e j) * dV ω (e i)
  rw [← dV_add hω, ← dV_add hω, add_comm]

theorem genS_pow (hω : ω ^ 3 = 1) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (i : Fin m) : genS he i ^ 3 = 1 :=
  Subtype.ext (by simpa [genS] using dV_pow_three_subS (τ := τ) hω (e i))

theorem vecProd_genS (hω : ω ^ 3 = 1) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (a : Fin m → ZMod 3) :
    vecProd (genS he) a = dS hω he a := by
  refine Subtype.ext ?_
  rw [vecProd, Subgroup.val_list_prod, List.map_map]
  change _ = dV ω (subLin e a)
  rw [dV_subLin hω]
  rfl

theorem pow_three_of_orderOf {M : Type*} [Monoid M] {x : M} (h : orderOf x = 3) : x ^ 3 = 1 := by
  rw [← h]
  exact pow_orderOf_eq_one x

theorem gLAPPrimeCoreOf_centralizer_subS (hω3 : orderOf ω = 3) {m : ℕ}
    {e : Fin m → Fin τ.rank → ZMod 3} (he : ∀ i, dV (τ := τ) ω (e i) ∈ G)
    (hinj : Function.Injective (subLin (τ := τ) e))
    (hleaf : ∀ fl ∈ normVecs 3 m,
      GLAPPrimeCoreOf 3 (famCentS ω G ((kerBasis 3 fl).map (liftL e))) = ⊥)
    (hstd : GLAPPrimeCoreOf 3 (famCentS ω G ((Native.stdBasis m).map (liftL e))) = ⊥)
    {y : Fin m → ZMod 3} (hy : y ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dS (pow_three_of_orderOf hω3) he y}) = ⊥ := by
  have hω : ω ^ 3 = 1 := pow_three_of_orderOf hω3
  set φ := vecProdHom (genS he) (genS_comm hω he) (genS_pow hω he) with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dS hω he a := fun a => vecProd_genS hω he a
  have hinjφ : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have h1 := dV_injective (τ := τ) hω3 (congrArg Subtype.val h)
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hinj h1]
  set A := φ.range with hAdef
  have hmemA : ∀ a, dS hω he a ∈ A := fun a => ⟨Multiplicative.ofAdd a, hφ a⟩
  have hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hA : IsElemAbelian 3 A := by
    refine ⟨⟨⟨fun x z => Subtype.ext (hAcomm x x.2 z z.2)⟩⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
      have h3 : (3 • Multiplicative.toAdd a) = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have : (3 : ZMod 3) = 0 := rfl
        rw [Nat.cast_ofNat, this, zero_mul]
      rw [h3, ofAdd_zero]
    rw [this, map_one]
  have hAC : A ≤ Subgroup.centralizer {dS hω he y} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm x hx _ (hmemA y)
  have hA1 : A ≠ ⊥ := by
    intro h
    have h1 : dS hω he y ∈ (⊥ : Subgroup G) := h ▸ hmemA y
    rw [Subgroup.mem_bot] at h1
    have h2 : dV ω (subLin e y) = dV ω (subLin e 0) := by
      rw [subLin_zero, dV_zero]
      exact congrArg Subtype.val h1
    exact hy (hinj (dV_injective (τ := τ) hω3 h2))
  have hcentB : ∀ (kb : List (List ℕ)), Subgroup.centralizer
      (Subgroup.closure {x | ∃ b ∈ kb, x = vecProd (genS he) (listVec m b)} : Set G) =
        famCentS ω G (kb.map (liftL e)) := by
    intro kb
    rw [Subgroup.centralizer_closure]
    ext x
    rw [Subgroup.mem_centralizer_iff, mem_famCentS]
    constructor
    · intro h j
      have hj : (kb.map (liftL e)).get j = liftL e (kb.get ⟨j.val, by simpa using j.2⟩) := by
        simp
      rw [hj, listVec_liftL]
      have h1 := h _ ⟨kb.get ⟨j.val, by simpa using j.2⟩, List.get_mem kb _,
        (vecProd_genS hω he _).symm⟩
      exact (congrArg Subtype.val h1).symm
    · rintro h _ ⟨b, hb, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem hb
      rw [vecProd_genS hω he]
      have hj := h ⟨j.val, by simp⟩
      have e1 : (kb.map (liftL e)).get ⟨j.val, by simp⟩ = liftL e (kb.get j) := by simp
      rw [e1, listVec_liftL] at hj
      exact Subtype.ext hj.symm
  have hcentA : ∀ x : G, (∀ z ∈ A, z * x = x * z) ↔
      x ∈ famCentS ω G ((Native.stdBasis m).map (liftL e)) := by
    intro x
    rw [mem_famCentS]
    constructor
    · intro h j
      have hj : ((Native.stdBasis m).map (liftL e)).get j =
          liftL e ((Native.stdBasis m).get ⟨j.val, by simpa using j.2⟩) := by
        simp
      rw [hj, listVec_liftL]
      have h1 := h _ (hmemA (listVec m ((Native.stdBasis m).get ⟨j.val, by simpa using j.2⟩)))
      exact (congrArg Subtype.val h1).symm
    · intro h z hz
      obtain ⟨a, rfl⟩ := hz
      have hgen : ∀ i, genS he i ∈ Subgroup.centralizer {x} := by
        intro i
        have hj := h ⟨i.val, by simp [length_stdBasis']⟩
        have e1 : ((Native.stdBasis m).map (liftL e)).get ⟨i.val, by simp [length_stdBasis']⟩ =
            liftL e ((Native.stdBasis m).get ⟨i.val, by simp [length_stdBasis']⟩) := by simp
        rw [e1, listVec_liftL, listVec_stdBasis', subLin_single] at hj
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext hj.symm
      have hz : φ a ∈ Subgroup.centralizer {x} := by
        rw [← ofAdd_toAdd a, hφdef, vecProdHom_apply, vecProd]
        refine Subgroup.list_prod_mem (K := Subgroup.centralizer {x}) fun g hg => ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        exact pow_mem (hgen i) _
      exact (Subgroup.mem_centralizer_singleton_iff.1 hz)
  refine gLAPPrimeCoreOf_eq_bot_of_hyperplanes Nat.prime_three hA hAC hA1 fun B hBA hidx => ?_
  obtain ⟨fl, hfl, hBeq⟩ := exists_normVec_eq_closure (genS_comm hω he) (genS_pow hω he) hinjφ
    hBA hidx
  by_cases hxB : dS hω he y ∈ B
  · have hle : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer {dS hω he y} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxB)
    rw [inf_eq_right.2 hle, hBeq, hcentB]
    exact hleaf fl hfl
  · have heq : Subgroup.centralizer {dS hω he y} ⊓ Subgroup.centralizer (B : Set G) =
        famCentS ω G ((Native.stdBasis m).map (liftL e)) := by
      ext x
      rw [Subgroup.mem_inf, ← hcentA]
      constructor
      · rintro ⟨h1, h2⟩ z hz
        have hz' := le_sup_zpowers_of_relIndex hBA hidx (hmemA y) hxB hz
        have hle : B ⊔ Subgroup.zpowers (dS hω he y) ≤ Subgroup.centralizer {x} := by
          refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 h2 b hb)) ?_
          rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_singleton_iff.1 h1).symm
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz')
      · intro h
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (h _ (hmemA y)).symm,
          Subgroup.mem_centralizer_iff.2 fun z hz => h z (hBA hz)⟩
    rw [heq]
    exact hstd

end Assembly

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
