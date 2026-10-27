module

public import CFSG.GF2Type.Smith1979.W4C1Chain
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import Certificates.Certificate330375

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U Subgroup

theorem chk_parts (h : chk = true) :
    syP.all pairCheck = true ∧ closureOK syG syT 512 = true ∧ syT.contains w2C = true ∧
      (!(w2C == one6)) = true ∧ chainOK = true := by
  simp only [chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

variable (hP : syP.all pairCheck = true)

@[expose] def Sy : Subgroup H6 :=
  Subgroup.closure (genSet syP hP)

@[expose] def Rep (c : List ℕ) (g : H6) : Prop :=
  canon6 c = true ∧ dec6 c = mat6 g

variable {hP}

theorem Rep.mul {a b : List ℕ} {g h : H6} (ha : Rep a g) (hb : Rep b h) :
    Rep (mul6 a b) (g * h) :=
  ⟨canon6_mul6 _ _, by rw [dec6_mul6, ha.2, hb.2, map_mul]⟩

theorem rep_one : Rep one6 1 :=
  ⟨canon6_one6, by rw [dec6_one6, map_one]⟩

theorem Rep.eq_iff {a b : List ℕ} {g h : H6} (ha : Rep a g) (hb : Rep b h) : a = b ↔ g = h := by
  constructor
  · rintro rfl
    exact mat6_injective (ha.2.symm.trans hb.2)
  · rintro rfl
    exact dec6_injective ha.1 hb.1 (ha.2.trans hb.2.symm)

theorem syG_rep (hP : syP.all pairCheck = true) : ∀ c ∈ syG, ∃ g ∈ Sy hP, Rep c g := by
  intro c hc
  obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp hc
  refine ⟨ofCode cc (List.all_eq_true.mp hP cc hcc), ofCode_mem_closure hP hcc, ?_, ?_⟩
  · exact (pairCheck_spec (List.all_eq_true.mp hP cc hcc)).1
  · exact (mat6_ofCode _ _).symm

theorem exists_elt_of_table (hP : syP.all pairCheck = true) (hok : closureOK syG syT 512 = true)
    {c : List ℕ} (hc : c ∈ syT.toList) : ∃ g ∈ Sy hP, Rep c g := by
  obtain ⟨t, ht, hct⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hc)
  have hget : syT.getD t [] = c := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some, hct]
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨hsize, hclosed⟩, hdist⟩, hcanon⟩ := hok
  have himg := image_closure_eq dec6 one6 mul6 syG mat6 dec6_one6 dec6_mul6 (genSet syP hP)
    (image_genSet syP hP) _ hclosed
  have hmem : dec6 c ∈ mat6 '' (Subgroup.closure (genSet syP hP) : Set H6) := by
    rw [himg]
    exact ⟨t, ht, congrArg dec6 hget⟩
  obtain ⟨g, hg, hge⟩ := hmem
  refine ⟨g, hg, ?_, hge.symm⟩
  have := allCheck_spec hcanon ht
  rwa [hget] at this

theorem exists_rep_of_mem (hP : syP.all pairCheck = true) (hok : closureOK syG syT 512 = true)
    {g : H6} (hg : g ∈ Sy hP) : ∃ c ∈ syT.toList, Rep c g := by
  obtain ⟨t, ht, hdec, hcan⟩ := exists_code_closure syP hP 512 hok hg
  have ht' : t < syT.size := ht
  refine ⟨syT.getD t [], ?_, hcan, hdec⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht', Option.getD_some]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem ht')

theorem card_Sy (hP : syP.all pairCheck = true) (hok : closureOK syG syT 512 = true) :
    Nat.card (Sy hP) = 512 :=
  card_closure_genSet syP hP 512 hok

section ChainCodes

variable {hP : syP.all pairCheck = true}

theorem centralInv_of_chain {z : Sy hP} {cz : List ℕ} (rz : Rep cz (z : H6)) {x y : Sy hP}
    (h : Chain z x y) : centralInv cz = true := by
  have hone : Rep one6 (1 : H6) := rep_one
  simp only [centralInv, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, fun s hs => ?_⟩
  · refine (rz.mul rz |>.eq_iff hone).mpr ?_
    simpa using congrArg Subtype.val h.z_sq
  · rw [Bool.eq_false_iff]
    intro hc
    have := (rz.eq_iff hone).mp (beq_iff_eq.mp hc)
    exact h.z_ne (Subtype.ext this)
  · obtain ⟨g, hg, rg⟩ := syG_rep hP s hs
    refine (((rg.mul rz).eq_iff (rz.mul rg))).mpr ?_
    simpa using congrArg Subtype.val (h.z_cent ⟨g, hg⟩)

theorem bEq {a b : List ℕ} {g h : H6} (ra : Rep a g) (rb : Rep b h) (e : g = h) :
    (a == b) = true :=
  beq_iff_eq.mpr ((ra.eq_iff rb).mpr e)

theorem bNe {a b : List ℕ} {g h : H6} (ra : Rep a g) (rb : Rep b h) (e : g ≠ h) :
    (!(a == b)) = true := by
  cases h' : (a == b)
  · rfl
  · exact absurd ((ra.eq_iff rb).mp (beq_iff_eq.mp h')) e

theorem condX_of_chain {z x y : Sy hP} {cz cx : List ℕ} (rz : Rep cz (z : H6))
    (rx : Rep cx (x : H6)) (h : Chain z x y) : condX cz cx = true := by
  have hone : Rep one6 (1 : H6) := rep_one
  simp only [condX, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact bEq (rx.mul rx) hone (by simpa using congrArg Subtype.val h.x_sq)
  · exact bNe rx hone (fun e => h.x_ne (Subtype.ext e))
  · exact bNe rx rz (fun e => h.x_ne_z (Subtype.ext e))
  · exact bEq (rx.mul rz) (rz.mul rx) (by simpa using congrArg Subtype.val h.x_comm)
  · refine List.all_eq_true.mpr fun s hs => ?_
    obtain ⟨g, hg, rg⟩ := syG_rep hP s hs
    refine Bool.or_eq_true_iff.mpr ?_
    rcases h.x_conj ⟨g, hg⟩ with h1 | h1
    · exact Or.inl (bEq (rg.mul rx) (rx.mul rg) (by simpa using congrArg Subtype.val h1))
    · exact Or.inr (bEq (rg.mul rx) ((rx.mul rz).mul rg)
        (by simpa [mul_assoc] using congrArg Subtype.val h1))

theorem condY_of_chain {z x y : Sy hP} {cz cx cy : List ℕ} (rz : Rep cz (z : H6))
    (rx : Rep cx (x : H6)) (ry : Rep cy (y : H6)) (h : Chain z x y) :
    condY cz cx cy = true := by
  have hone : Rep one6 (1 : H6) := rep_one
  simp only [condY, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact bEq (ry.mul ry) hone (by simpa using congrArg Subtype.val h.y_sq)
  · exact bNe ry hone (fun e => h.y_ne (Subtype.ext e))
  · exact bNe ry rz (fun e => h.y_ne_z (Subtype.ext e))
  · exact bNe ry rx (fun e => h.y_ne_x (Subtype.ext e))
  · exact bNe ry (rx.mul rz) (fun e => h.y_ne_xz (Subtype.ext (by simpa using e)))
  · exact bEq (ry.mul rz) (rz.mul ry) (by simpa using congrArg Subtype.val h.y_comm_z)
  · exact bEq (ry.mul rx) (rx.mul ry) (by simpa using congrArg Subtype.val h.y_comm_x)
  · refine List.all_eq_true.mpr fun s hs => ?_
    obtain ⟨g, hg, rg⟩ := syG_rep hP s hs
    simp only [Bool.or_eq_true, or_assoc]
    rcases h.y_conj ⟨g, hg⟩ with h1 | h1 | h1 | h1
    · exact Or.inl (bEq (rg.mul ry) (ry.mul rg) (by simpa using congrArg Subtype.val h1))
    · exact Or.inr (Or.inl (bEq (rg.mul ry) ((ry.mul rz).mul rg)
        (by simpa [mul_assoc] using congrArg Subtype.val h1)))
    · exact Or.inr (Or.inr (Or.inl (bEq (rg.mul ry) ((ry.mul rx).mul rg)
        (by simpa [mul_assoc] using congrArg Subtype.val h1))))
    · exact Or.inr (Or.inr (Or.inr (bEq (rg.mul ry) ((ry.mul (rx.mul rz)).mul rg)
        (by simpa [mul_assoc] using congrArg Subtype.val h1))))

theorem chainOK_apply (hch : chainOK = true) {cz cx cy : List ℕ} (hcz : cz ∈ syT.toList)
    (hcx : cx ∈ syT.toList) (hcy : cy ∈ syT.toList) (h1 : centralInv cz = true)
    (h2 : condX cz cx = true) (h3 : condY cz cx cy = true) : inT8 cz cx cy w2C = true := by
  have a1 := List.all_eq_true.mp (by simpa only [chainOK] using hch) cz hcz
  simp only [h1, Bool.not_true, Bool.false_or] at a1
  have a2 := List.all_eq_true.mp a1 cx hcx
  simp only [h2, Bool.not_true, Bool.false_or] at a2
  have a3 := List.all_eq_true.mp a2 cy hcy
  simp only [h3, Bool.not_true, Bool.false_or] at a3
  exact a3


theorem exists_w :
    ∃ hP : syP.all pairCheck = true, Nat.card (Sy hP) = 512 ∧
      ∃ w : Sy hP, w ≠ 1 ∧ ∀ z x y : Sy hP, Chain z x y → w ∈ T8 z x y := by
  obtain ⟨hP, hok, hw2, hw1, hch⟩ := chk_parts Certificates.certificate330375
  refine ⟨hP, card_Sy hP hok, ?_⟩
  have hw2' : w2C ∈ syT.toList := by
    simpa using hw2
  obtain ⟨w, hwSy, rw⟩ := exists_elt_of_table hP hok hw2'
  have hone : Rep one6 (1 : H6) := rep_one
  refine ⟨⟨w, hwSy⟩, ?_, ?_⟩
  · intro h1
    have : w2C = one6 := (rw.eq_iff hone).mpr (by simpa using congrArg Subtype.val h1)
    simp [this] at hw1
  · intro z x y hC
    obtain ⟨cz, hcz, rz⟩ := exists_rep_of_mem hP hok z.2
    obtain ⟨cx, hcx, rx⟩ := exists_rep_of_mem hP hok x.2
    obtain ⟨cy, hcy, ry⟩ := exists_rep_of_mem hP hok y.2
    have h8 := chainOK_apply hch hcz hcx hcy (centralInv_of_chain rz hC)
      (condX_of_chain rz rx hC) (condY_of_chain rz rx ry hC)
    simp only [inT8, Bool.or_eq_true, beq_iff_eq, or_assoc] at h8
    simp only [T8, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h8 with h | h | h | h | h | h | h | h
    · exact Or.inl (Subtype.ext (by simpa using (rw.eq_iff hone).mp h))
    · exact Or.inr (Or.inl (Subtype.ext (by simpa using (rw.eq_iff rz).mp h)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa using (rw.eq_iff rx).mp h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        (Subtype.ext (by simpa using (rw.eq_iff (rx.mul rz)).mp h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Subtype.ext (by simpa using (rw.eq_iff ry).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Subtype.ext (by simpa using (rw.eq_iff (ry.mul rz)).mp h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Subtype.ext (by simpa using (rw.eq_iff (ry.mul rx)).mp h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Subtype.ext (by simpa using (rw.eq_iff (ry.mul (rx.mul rz))).mp h))))))))

end ChainCodes

theorem nonempty_mulEquiv_Sy (hP : syP.all pairCheck = true) (hSy : Nat.card (Sy hP) = 512)
    {Γ : Type*} [Group Γ] [Finite Γ] (ι : Γ →* H6) (hι : Function.Injective ι)
    (T : Subgroup Γ) (hT : Nat.card T = 512) : Nonempty (T ≃* Sy hP) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup H6 := T.map ι with hT'def
  have hT' : Nat.card T' = 512 := (Subgroup.card_map_of_injective hι).trans hT
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  have hp : IsPGroup 2 T' := IsPGroup.of_card (by rw [hT', h512])
  have hpSy : IsPGroup 2 (Sy hP) := IsPGroup.of_card (by rw [hSy, h512])
  have hidx : ∀ A : Subgroup H6, Nat.card A = 512 → ¬ 2 ∣ A.index := by
    intro A hA h2
    have h1 := Subgroup.card_mul_index A
    rw [hA, card_H6] at h1
    have h3 : A.index = 2835 := by omega
    rw [h3] at h2
    omega
  let PT : Sylow 2 H6 := hp.toSylow (hidx T' hT')
  let PS : Sylow 2 H6 := hpSy.toSylow (hidx _ hSy)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H6 PT PS
  have hconj : T'.map (MulAut.conj c).toMonoidHom = Sy hP := by
    have h1 : ((c • PT : Sylow 2 H6) : Subgroup H6) = (PS : Subgroup H6) := by rw [hc]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  exact ⟨(T.equivMapOfInjective ι hι).trans
    ((T'.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hconj))⟩

theorem T8_subset {S : Type*} [Group S] {F : Subgroup S} {z x y : S} (hz : z ∈ F) (hx : x ∈ F)
    (hy : y ∈ F) : T8 z x y ⊆ (F : Set S) := by
  intro w hw
  simp only [T8, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact F.one_mem
  · exact hz
  · exact hx
  · exact F.mul_mem hx hz
  · exact hy
  · exact F.mul_mem hy hz
  · exact F.mul_mem hy hx
  · exact F.mul_mem hy (F.mul_mem hx hz)

theorem sylow_normal_elemAb_mem {Γ : Type*} [Group Γ] [Finite Γ]
    (ι : Γ →* H6) (hι : Function.Injective ι) (T : Subgroup Γ) (hT : Nat.card T = 512) :
    ∃ w ∈ T, w ≠ 1 ∧ ∀ F : Subgroup Γ, F ≤ T → (∀ t ∈ T, ∀ f ∈ F, t * f * t⁻¹ ∈ F) →
      (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) → (∀ a ∈ F, a * a = 1) → 8 ≤ Nat.card F → w ∈ F := by
  obtain ⟨hP, hSy, w₀, hw₀1, hw₀⟩ := exists_w
  obtain ⟨φ⟩ := nonempty_mulEquiv_Sy hP hSy ι hι T hT
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 9) (by rw [hT]; norm_num)
  refine ⟨((φ.symm w₀ : T) : Γ), (φ.symm w₀).2, ?_, ?_⟩
  · intro h
    apply hw₀1
    have h1 : φ.symm w₀ = 1 := Subtype.ext h
    rw [← φ.symm.map_eq_one_iff]
    exact h1
  · intro F hFT hFn hFc hFs hF8
    set FT : Subgroup T := F.subgroupOf T with hFT_def
    have hFTn : FT.Normal :=
      ⟨fun f hf t => by
        rw [hFT_def, Subgroup.mem_subgroupOf] at hf ⊢
        simpa using hFn t t.2 f hf⟩
    have hcard : Nat.card FT = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv
    obtain ⟨z, x, y, hC, hzF, hxF, hyF⟩ := exists_chain hTp FT hFTn
      (fun a ha b hb => Subtype.ext (hFc a ((Subgroup.mem_subgroupOf).mp ha) b
        ((Subgroup.mem_subgroupOf).mp hb)))
      (fun a ha => Subtype.ext (hFs a ((Subgroup.mem_subgroupOf).mp ha)))
      (by rw [hcard]; exact hF8)
    have h1 := mem_T8_map φ (hw₀ _ _ _ (hC.map φ))
    have h2 := T8_subset hzF hxF hyF h1
    exact (Subgroup.mem_subgroupOf).mp h2

end CFSG.GF2Type.Smith1979.W4C1
