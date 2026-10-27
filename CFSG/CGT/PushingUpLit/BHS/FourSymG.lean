module

public import CFSG.CGT.PushingUpLit.BHS.FourSymD
public import CFSG.CGT.PushingUpLit.BHS.FourSymB

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V]

@[expose] def cenD (D : Set (Subgroup (MulAut V))) (Z : Subgroup (MulAut V)) :
    Set (Subgroup (MulAut V)) :=
  {X | X ∈ D ∧ X ≠ Z ∧ ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x}

@[expose] def AdjIn (S : Set (Subgroup (MulAut V))) (X Y : Subgroup (MulAut V)) : Prop :=
  X ∈ S ∧ Y ∈ S ∧ NonComm X Y

@[expose] def ConnIn (S : Set (Subgroup (MulAut V))) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, Relation.ReflTransGen (AdjIn S) X Y

@[expose] def JFam (D : Set (Subgroup (MulAut V))) (A : Subgroup (MulAut V)) :
    Set (Set (Subgroup (MulAut V))) :=
  {S | S.Nonempty ∧ S ⊆ cenD D A ∧ ConnIn S}

theorem NonComm.symm' {A B : Subgroup (MulAut V)} (h : NonComm A B) : NonComm B A := by
  obtain ⟨a, ha, b, hb, hne⟩ := h
  exact ⟨b, hb, a, ha, fun e => hne e.symm⟩

theorem NonComm.conj' {A B : Subgroup (MulAut V)} (h : NonComm A B) (g : MulAut V) :
    NonComm (conjSub g A) (conjSub g B) := by
  obtain ⟨a, ha, b, hb, hne⟩ := h
  refine ⟨g * a * g⁻¹, mem_conjSub_of_mem ha, g * b * g⁻¹, mem_conjSub_of_mem hb, fun e => hne ?_⟩
  have := congrArg (fun z => g⁻¹ * z * g) e
  simpa [mul_assoc] using this

theorem AdjIn.mono {S S' : Set (Subgroup (MulAut V))} (h : S ⊆ S') {X Y : Subgroup (MulAut V)}
    (hXY : AdjIn S X Y) : AdjIn S' X Y :=
  ⟨h hXY.1, h hXY.2.1, hXY.2.2⟩

theorem connIn_insert {S : Set (Subgroup (MulAut V))} (hS : ConnIn S) {X Y : Subgroup (MulAut V)}
    (hX : X ∈ S) (hnc : NonComm X Y) : ConnIn (insert Y S) := by
  have hadj : ∀ A B : Subgroup (MulAut V), AdjIn S A B → AdjIn (insert Y S) A B :=
    fun A B hAB => hAB.mono (Set.subset_insert Y S)
  have hmono : ∀ U W : Subgroup (MulAut V), U ∈ S → W ∈ S →
      Relation.ReflTransGen (AdjIn (insert Y S)) U W := fun U W hU hW =>
    Relation.ReflTransGen.mono hadj U W (hS U hU W hW)
  have hYX : Relation.ReflTransGen (AdjIn (insert Y S)) Y X :=
    Relation.ReflTransGen.single ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ hX, hnc.symm'⟩
  have hXY : Relation.ReflTransGen (AdjIn (insert Y S)) X Y :=
    Relation.ReflTransGen.single ⟨Set.mem_insert_of_mem _ hX, Set.mem_insert _ _, hnc⟩
  intro U hU W hW
  rcases hU with rfl | hU <;> rcases hW with rfl | hW
  · exact Relation.ReflTransGen.refl
  · exact hYX.trans (hmono X W hX hW)
  · exact (hmono U X hU hX).trans hXY
  · exact hmono U W hU hW

theorem ConnIn.image_conj {S : Set (Subgroup (MulAut V))} (hS : ConnIn S) (g : MulAut V) :
    ConnIn (conjSub g '' S) := by
  rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
  have := hS X hX Y hY
  induction this with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact (ih hbc.1).tail ⟨⟨_, hbc.1, rfl⟩, ⟨_, hbc.2.1, rfl⟩, hbc.2.2.conj' g⟩

section Cen

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem cenD_conj (h : Hyp41 P D) {Z X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P)
    (hX : X ∈ cenD D Z) : conjSub g X ∈ cenD D (conjSub g Z) := by
  refine ⟨h.conj_mem X hX.1 g hg, fun heq => hX.2.1 ?_, ?_⟩
  · have := congrArg (conjSub g⁻¹) heq
    rwa [FourTwoTools.conjSub_inv_conjSub, FourTwoTools.conjSub_inv_conjSub] at this
  · intro y hy z hz
    rw [mem_conjSub_iff] at hy hz
    have e := hX.2.2 _ hy _ hz
    calc y * z = g * (g⁻¹ * y * g) * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * (g⁻¹ * y * g) * g⁻¹ := by
        rw [mul_assoc g (g⁻¹ * y * g), e, ← mul_assoc]
      _ = z * y := by group

theorem cenD_conj_of_cen (h : Hyp41 P D) {A X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ P)
    (hgA : ∀ a ∈ A, g * a = a * g) (hX : X ∈ cenD D A) : conjSub g X ∈ cenD D A := by
  have hA : conjSub g A = A := FourOneTools.conjSub_eq_of_comm hgA
  have := cenD_conj h hg hX
  rwa [hA] at this

theorem le_centralizer_of_mem_cenD {A X : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
    (hX : X ∈ cenD D A) : X ≤ Subgroup.centralizer (A : Set (MulAut V)) := fun x hx =>
  Subgroup.mem_centralizer_iff.2 fun a ha => (hX.2.2 x hx a ha).symm

variable [Finite V]

theorem Hyp41.noncomm_conj (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1) {X Y : Subgroup (MulAut V)}
    (hX : X ∈ D) (hY : Y ∈ D) (hX2 : Nat.card X = 2) (hY2 : Nat.card Y = 2)
    (hnc : NonComm X Y) {g : MulAut V} (hg : g ∈ Y) (hg1 : g ≠ 1) :
    NonComm X (conjSub g X) := by
  obtain ⟨x, u, hx, -, hXx, -⟩ := exists_transv_of_card_two h hV hX hX2
  obtain ⟨y, w, hy, -, hYy, -⟩ := exists_transv_of_card_two h hV hY hY2
  have hnc' : x * y ≠ y * x := fun hc => by
    obtain ⟨a, ha, b, hb, hne⟩ := hnc
    rw [hXx] at ha
    rw [hYy] at hb
    exact hne ((forall_comm_zpowers_iff x y).2 hc a ha b hb)
  obtain ⟨hxw, hyu, huw⟩ := Hyp41.rel_of_noncomm h hV hX hY hx hy hXx hYy hnc'
  have hgy : g = y := by
    rw [hYy] at hg
    rcases eq_one_or_of_mem_zpowers hy.sq hg with h1 | h1
    · exact absurd h1 hg1
    · exact h1
  subst hgy
  refine ⟨x, ?_, g * x * g⁻¹, ?_, ?_⟩
  · rw [hXx]
    exact Subgroup.mem_zpowers x
  · rw [hXx, conjSub_zpowers]
    exact Subgroup.mem_zpowers _
  · intro hc
    have hx' := hx.conj g
    have := ((IsTransv.comm_iff hV hx hx').1 hc).1
    rw [hyu, map_mul, hx.apply_centre hV, hxw] at this
    have hu2 : u * u = 1 := by rw [← pow_two]; exact hV u
    have h3 : w * u = w := mul_left_cancel this
    exact hx.ne (mul_left_cancel (h3.trans (mul_one w).symm))

@[expose] def IsMaxJ (D : Set (Subgroup (MulAut V))) (A : Subgroup (MulAut V))
    (S : Set (Subgroup (MulAut V))) : Prop :=
  S ∈ JFam D A ∧ ∀ S' ∈ JFam D A, S'.ncard ≤ S.ncard

theorem IsMaxJ.adj_mem {D : Set (Subgroup (MulAut V))} {A : Subgroup (MulAut V)}
    {S : Set (Subgroup (MulAut V))} (hS : IsMaxJ D A S) {X Y : Subgroup (MulAut V)}
    (hX : X ∈ S) (hY : Y ∈ cenD D A) (hnc : NonComm X Y) : Y ∈ S := by
  by_contra hYS
  have hmem : insert Y S ∈ JFam D A :=
    ⟨⟨Y, Set.mem_insert _ _⟩, Set.insert_subset hY hS.1.2.1, connIn_insert hS.1.2.2 hX hnc⟩
  have h1 := hS.2 _ hmem
  rw [Set.ncard_insert_of_notMem hYS (Set.toFinite S)] at h1
  omega

theorem IsMaxJ.mem_of_noncomm {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hS2 : ∀ X ∈ D, Nat.card X = 2) (hconn : ConnD D)
    {A : Subgroup (MulAut V)} (hAD : A ∈ D) (hAM : A ≤ M) {S : Set (Subgroup (MulAut V))}
    (hS : IsMaxJ D A S) {B : Subgroup (MulAut V)} (hB : B ∈ cenD D A) (hBM : B ≤ M)
    (hBS : B ∉ S) {Z : Subgroup (MulAut V)} (hZ : Z ∈ D) (hZM : ¬ Z ≤ M)
    {X : Subgroup (MulAut V)} (hX : X ∈ S) (hZX : NonComm Z X) : Z ∈ S := by
  have hZA : Z ≠ A := fun e => hZM (e ▸ hAM)
  by_cases hBZ : NonComm B Z
  · have hL := lamSet_of_noncomm_pair h.toHyp41 hV hB.1 hZ (hS2 B hB.1) (hS2 Z hZ) hBZ hBM hZM
    have hcomm := four_fifteen_M h hV hB.1 hAD hBM hAM hB.2.1 hB.2.2 hL le_sup_left
      (fun hle => hZM (le_sup_right.trans hle))
    have hZcen : Z ∈ cenD D A :=
      ⟨hZ, hZA, fun z hz a ha => hcomm z (Subgroup.mem_sup_right hz) a ha⟩
    exact hS.adj_mem hX hZcen hZX.symm'
  · by_contra hZS
    have hBZ' : ∀ b ∈ B, ∀ z ∈ Z, b * z = z * b := by
      by_contra hcon
      push Not at hcon
      exact hBZ hcon
    have hZB : Z ∈ cenD D B :=
      ⟨hZ, fun e => hZM (e ▸ hBM), fun z hz b hb => (hBZ' b hb z hz).symm⟩
    have hSB : S ⊆ cenD D B := by
      intro X' hX'
      refine ⟨(hS.1.2.1 hX').1, fun e => hBS (e ▸ hX'), fun x hx b hb => ?_⟩
      by_contra hne
      exact hBS (hS.adj_mem hX' hB ⟨x, hx, b, hb, hne⟩)
    have hins : insert Z S ⊆ cenD D B := Set.insert_subset hZB hSB
    have hconn2 : ConnIn (insert Z S) := connIn_insert hS.1.2.2 hX hZX.symm'
    obtain ⟨g, hg, hgB⟩ := h.toHyp41.exists_conj_of_connD hconn hB.1 hAD
    have hS3 : conjSub g '' insert Z S ∈ JFam D A := by
      refine ⟨⟨_, Set.mem_image_of_mem _ (Set.mem_insert Z S)⟩, ?_, hconn2.image_conj g⟩
      rintro _ ⟨Y, hY, rfl⟩
      have := cenD_conj h.toHyp41 hg (hins hY)
      rwa [← hgB] at this
    have h1 := hS.2 _ hS3
    rw [Set.ncard_image_of_injective _ (FourTwoTools.conjSub_injective g),
      Set.ncard_insert_of_notMem hZS (Set.toFinite S)] at h1
    omega

theorem connIn_cenD {P : Subgroup (MulAut V)}
    {D : Set (Subgroup (MulAut V))} {T M : Subgroup (MulAut V)} (h : Hyp43 P D T M)
    (hV : ∀ v : V, v ^ 2 = 1) (hS2 : ∀ X ∈ D, Nat.card X = 2) (hconn : ConnD D)
    (hP : P ≤ ⨆ X ∈ D, X) {A T₀ : Subgroup (MulAut V)} (hAD : A ∈ D) (hAM : A ≤ M)
    (hT₀ : IsSylowOf 2 T₀ (P ⊓ Subgroup.centralizer (A : Set (MulAut V)))) (hT₀M : T₀ ≤ M) :
    ConnIn (cenD D A) := by
  by_contra hnc
  obtain ⟨X₀, hX₀⟩ : (cenD D A).Nonempty := by
    by_contra hemp
    exact hnc fun X hX => absurd ⟨X, hX⟩ hemp
  have hJne : (JFam D A).Nonempty :=
    ⟨{X₀}, ⟨X₀, rfl⟩, Set.singleton_subset_iff.2 hX₀, fun X hX Y hY => by
      rw [Set.mem_singleton_iff] at hX hY
      rw [hX, hY]⟩
  obtain ⟨S₀, hS₀J, hS₀max⟩ := Set.exists_max_image (JFam D A) Set.ncard (Set.toFinite _) hJne
  obtain ⟨Y₀, hY₀, hY₀S⟩ : ∃ Y ∈ cenD D A, Y ∉ S₀ := by
    by_contra hall
    push Not at hall
    apply hnc
    have : cenD D A = S₀ := Set.Subset.antisymm hall hS₀J.2.1
    rw [this]
    exact hS₀J.2.2
  have hY₀H : Y₀ ≤ P ⊓ Subgroup.centralizer (A : Set (MulAut V)) :=
    le_inf (h.le Y₀ hY₀.1) (le_centralizer_of_mem_cenD hY₀)
  have hY₀2 : IsPGroup 2 ↥Y₀ := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb Y₀ hY₀.1).2
  obtain ⟨g₀, hg₀H, hY₀g⟩ := FourTwoTools.exists_conjSub_ge hT₀ hY₀2 hY₀H
  have hg₀P : g₀ ∈ P := hg₀H.1
  have hg₀A : ∀ a ∈ A, g₀⁻¹ * a = a * g₀⁻¹ := fun a ha =>
    (Commute.inv_left (show Commute g₀ a from
      (Subgroup.mem_centralizer_iff.1 hg₀H.2 a ha).symm)).eq
  have hgP : g₀⁻¹ ∈ P := P.inv_mem hg₀P
  set S' : Set (Subgroup (MulAut V)) := conjSub g₀⁻¹ '' S₀ with hS'
  have hS'J : S' ∈ JFam D A := by
    refine ⟨⟨_, Set.mem_image_of_mem _ hS₀J.1.some_mem⟩, ?_, hS₀J.2.2.image_conj _⟩
    rintro _ ⟨Y, hY, rfl⟩
    exact cenD_conj_of_cen h.toHyp41 hgP hg₀A (hS₀J.2.1 hY)
  have hncard : S'.ncard = S₀.ncard :=
    Set.ncard_image_of_injective _ (FourTwoTools.conjSub_injective _)
  have hmax : IsMaxJ D A S' := ⟨hS'J, fun S'' hS'' => hncard ▸ hS₀max S'' hS''⟩
  have hBcen : conjSub g₀⁻¹ Y₀ ∈ cenD D A := cenD_conj_of_cen h.toHyp41 hgP hg₀A hY₀
  have hBM : conjSub g₀⁻¹ Y₀ ≤ M := by
    have := conjSub_mono g₀⁻¹ hY₀g
    rw [FourTwoTools.conjSub_inv_conjSub] at this
    exact this.trans hT₀M
  have hBS : conjSub g₀⁻¹ Y₀ ∉ S' := by
    rintro ⟨X, hX, hXe⟩
    exact hY₀S (FourTwoTools.conjSub_injective _ hXe ▸ hX)
  have hnormS : ∀ Z ∈ D, ¬ Z ≤ M → ∀ z ∈ Z, ∀ X ∈ S', conjSub z X ∈ S' := by
    intro Z hZ hZM z hz X hX
    by_cases hcom : ∀ a ∈ Z, ∀ b ∈ X, a * b = b * a
    · rw [FourOneTools.conjSub_eq_of_comm fun x hx => hcom z hz x hx]
      exact hX
    · push Not at hcom
      have hZS : Z ∈ S' :=
        hmax.mem_of_noncomm h hV hS2 hconn hAD hAM hBcen hBM hBS hZ hZM hX hcom
      by_cases hz1 : z = 1
      · rw [hz1, conjSub_one]
        exact hX
      · have hXD : X ∈ D := (hS'J.2.1 hX).1
        have hnc2 := h.toHyp41.noncomm_conj hV hXD hZ (hS2 X hXD) (hS2 Z hZ)
          (show NonComm Z X from hcom).symm' hz hz1
        have hZcen : Z ∈ cenD D A := hS'J.2.1 hZS
        have hzA : ∀ a ∈ A, z * a = a * z := fun a ha => hZcen.2.2 z hz a ha
        exact hmax.adj_mem hX
          (cenD_conj_of_cen h.toHyp41 (h.le Z hZ hz) hzA (hS'J.2.1 hX)) hnc2
  have hcover : ∀ Z ∈ D, Z ≤ M ∨ Z ≤ setNormalizer P S' := by
    intro Z hZ
    by_cases hZM : Z ≤ M
    · exact Or.inl hZM
    · right
      intro z hz
      refine ⟨h.le Z hZ hz, fun X' => ⟨fun hX' => hnormS Z hZ hZM z hz X' hX', fun hX' => ?_⟩⟩
      have := hnormS Z hZ hZM z⁻¹ (Z.inv_mem hz) _ hX'
      rwa [FourTwoTools.conjSub_inv_conjSub] at this
  have hNP : setNormalizer P S' ≤ P := fun g hg => hg.1
  rcases two_one_rel h.M_le hNP h.conj_mem
      (fun X hX Y hY => h.toHyp41.exists_conj_of_connD hconn hX hY) hP hcover with hMP | hNP'
  · apply h.ne_core
    refine Set.Subset.antisymm (fun A' hA' => ?_) (fun A' hA' => hA'.1)
    refine ⟨hA', fun g hg => ?_⟩
    rw [hMP, conjSub_self_of_mem hg]
    exact h.le A' hA'
  · obtain ⟨X₁, hX₁⟩ := hS'J.1
    obtain ⟨g, hg, hgX⟩ := h.toHyp41.exists_conj_of_connD hconn (hS'J.2.1 hX₁).1 hAD
    have hgN : g ∈ setNormalizer P S' := by rw [hNP']; exact hg
    have hAS : A ∈ S' := by
      rw [hgX]
      exact (hgN.2 X₁).1 hX₁
    exact (hS'J.2.1 hAS).2.1 rfl

end Cen

end CFSG.CGT.PushingUpLit.BHS
