module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6LambdaDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Lambda2
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Count
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.McL
public import CFSG.LocalAnalysis.EvenSporadicStandard.LyStd.Ly
public import CFSG.Sporadic.Recognition.JankoWongSylow
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataMain

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

namespace Sec6SigOdd

section Groups

open CFSG.Open

open scoped Pointwise

section Basic

variable {G : Type*} [Group G]

@[expose] def IsFour (U : Subgroup G) : Prop := IsElemAbelian 2 U ∧ Nat.card U = 4

@[expose] def E8Adj (U V : Subgroup G) : Prop :=
  ∃ E : Subgroup G, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E ∧ V ≤ E ∧ Nat.card U = 4 ∧
    Nat.card V = 4

theorem E8Adj.symm {U V : Subgroup G} (h : E8Adj U V) : E8Adj V U := by
  obtain ⟨E, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨E, h1, h2, h4, h3, h6, h5⟩

theorem rtg_symm {U V : Subgroup G} (h : Relation.ReflTransGen E8Adj U V) :
    Relation.ReflTransGen E8Adj V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

theorem rtg_map_of {α β : Type*} {r : α → α → Prop} {p : β → β → Prop} (f : α → β)
    (hf : ∀ a b, r a b → p (f a) (f b)) {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen p (f a) (f b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hf _ _ hbc)

theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_isElemAbelian hE (hFE a.2) (hFE b.2))⟩⟩,
    fun x hx => hE.2 x (hFE hx)⟩

theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsPGroup 2 E :=
  fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem isElemAbelian_map' {G' : Type*} [Group G'] (f : G →* G') {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE f

theorem orderOf_eq_two_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E)
    (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (hE.2 x hx) hx1

theorem le_cen_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E) :
    E ≤ centralizer ({x} : Set G) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.2 (comm_of_isElemAbelian hE hy hx)

theorem isElemAbelian_of_sq {E : Subgroup G} (h : ∀ x ∈ E, x ^ 2 = 1) : IsElemAbelian 2 E := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, h⟩
  obtain ⟨x, hx⟩ := a
  obtain ⟨y, hy⟩ := b
  show x * y = y * x
  have hxx : x * x = 1 := by simpa [pow_two] using h x hx
  have hyy : y * y = 1 := by simpa [pow_two] using h y hy
  have hxy : x * y * (x * y) = 1 := by simpa [pow_two] using h _ (E.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have h1 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
  rw [h1, mul_inv_rev, hxi, hyi]

@[expose] def pairSub (u v : G) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huv : u * v = v * u) :
    Subgroup G where
  carrier := {1, u, v, u * v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have huu : u * u = 1 := by simpa [pow_two] using hu
    have hvv : v * v = 1 := by simpa [pow_two] using hv
    have e1 : u * (u * v) = v := by rw [← mul_assoc, huu, one_mul]
    have e2 : v * (u * v) = u := by rw [← mul_assoc, ← huv, mul_assoc, hvv, mul_one]
    have e3 : u * v * u = v := by rw [huv, mul_assoc, huu, mul_one]
    have e4 : u * v * v = u := by rw [mul_assoc, hvv, mul_one]
    have e5 : u * v * (u * v) = 1 := by rw [← mul_assoc, e3, hvv]
    have e6 : v * u = u * v := huv.symm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, huu, hvv, e1, e2, e3, e4, e5, e6, true_or, or_true]
  inv_mem' := by
    intro a ha
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hv)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hui]
    · simp [hvi]
    · rw [mul_inv_rev, hui, hvi]
      exact Or.inr (Or.inr (Or.inr huv.symm))

theorem left_mem_pairSub {u v : G} {hu : u ^ 2 = 1} {hv : v ^ 2 = 1} {huv : u * v = v * u} :
    u ∈ pairSub u v hu hv huv := Or.inr (Or.inl rfl)

theorem right_mem_pairSub {u v : G} {hu : u ^ 2 = 1} {hv : v ^ 2 = 1} {huv : u * v = v * u} :
    v ∈ pairSub u v hu hv huv := Or.inr (Or.inr (Or.inl rfl))

theorem pairSub_le {u v : G} {hu : u ^ 2 = 1} {hv : v ^ 2 = 1} {huv : u * v = v * u}
    {H : Subgroup G} (huH : u ∈ H) (hvH : v ∈ H) : pairSub u v hu hv huv ≤ H := by
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact huH
  · exact hvH
  · exact H.mul_mem huH hvH

theorem isElemAbelian_pairSub {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huv : u * v = v * u) :
    IsElemAbelian 2 (pairSub u v hu hv huv) := by
  refine isElemAbelian_of_sq fun x hx => ?_
  rcases hx with rfl | rfl | rfl | rfl
  · simp
  · exact hu
  · exact hv
  · have hc : Commute u v := huv
    rw [hc.mul_pow 2, hu, hv, one_mul]

theorem card_pairSub {u v : G} (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huv : u * v = v * u)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hne : u ≠ v) : Nat.card (pairSub u v hu hv huv) = 4 := by
  have huu : u * u = 1 := by simpa [pow_two] using hu
  have h1 : u * v ≠ 1 := fun h => hne (by
    have : v = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]; exact (inv_eq_of_mul_eq_one_right huu).symm)
  have h2 : u ≠ u * v := fun h => hv1 (by
    have := congrArg (fun w => u⁻¹ * w) h
    simpa using this.symm)
  have h3 : v ≠ u * v := fun h => hu1 (by
    have := congrArg (fun w => w * v⁻¹) h
    simpa using this.symm)
  have hc : Nat.card (pairSub u v hu hv huv) = ({1, u, v, u * v} : Set G).ncard :=
    Nat.card_coe_set_eq ({1, u, v, u * v} : Set G)
  rw [hc, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, h2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hu1.symm, hv1.symm, fun h => h1 h.symm⟩

theorem isFour_pairSub {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) (hne : u ≠ v)
    (huv : u * v = v * u) :
    IsFour (pairSub u v (hu ▸ pow_orderOf_eq_one u) (hv ▸ pow_orderOf_eq_one v) huv) :=
  ⟨isElemAbelian_pairSub _ _ huv,
    card_pairSub _ _ huv (fun h => by simp [h] at hu) (fun h => by simp [h] at hv) hne⟩

theorem exists_isFour_of_commute {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2)
    (hne : u ≠ v) (huv : u * v = v * u) {H : Subgroup G} (huH : u ∈ H) (hvH : v ∈ H) :
    ∃ U : Subgroup G, IsFour U ∧ u ∈ U ∧ v ∈ U ∧ U ≤ H :=
  ⟨_, isFour_pairSub hu hv hne huv, left_mem_pairSub, right_mem_pairSub, pairSub_le huH hvH⟩

end Basic

section Lift

variable {G G' : Type*} [Group G] [Group G']

theorem eq_of_inf_ker {f : G →* G'} {P : Subgroup G} (h : P ⊓ f.ker = ⊥) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) (hxy : f x = f y) : x = y := by
  have hmem : x * y⁻¹ ∈ P ⊓ f.ker := Subgroup.mem_inf.mpr ⟨P.mul_mem hx (P.inv_mem hy),
    MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel])⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

theorem card_map_of_inf_ker {f : G →* G'} {P : Subgroup G} (h : P ⊓ f.ker = ⊥) :
    Nat.card (P.map f) = Nat.card P :=
  (Nat.card_congr (Equiv.ofBijective (f.subgroupMap P)
    ⟨fun a b hab => Subtype.ext (eq_of_inf_ker h a.2 b.2 (congrArg Subtype.val hab)),
      f.subgroupMap_surjective P⟩)).symm

theorem isElemAbelian_of_map {f : G →* G'} {P : Subgroup G} (h : P ⊓ f.ker = ⊥)
    (hE : IsElemAbelian 2 (P.map f)) : IsElemAbelian 2 P := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · refine eq_of_inf_ker h (P.mul_mem a.2 b.2) (P.mul_mem b.2 a.2) ?_
    show f (↑a * ↑b) = f (↑b * ↑a)
    rw [map_mul, map_mul]
    exact comm_of_isElemAbelian hE (mem_map_of_mem f a.2) (mem_map_of_mem f b.2)
  · refine eq_of_inf_ker h (P.pow_mem hx 2) P.one_mem ?_
    rw [map_pow, map_one]
    exact hE.2 _ (mem_map_of_mem f hx)

theorem isFour_of_map {f : G →* G'} {P : Subgroup G} (h : P ⊓ f.ker = ⊥)
    (hP : IsFour (P.map f)) : IsFour P :=
  ⟨isElemAbelian_of_map h hP.1, (card_map_of_inf_ker h).symm.trans hP.2⟩

theorem isFour_map {f : G →* G'} {P : Subgroup G} (h : P ⊓ f.ker = ⊥) (hP : IsFour P) :
    IsFour (P.map f) :=
  ⟨isElemAbelian_map' f hP.1, (card_map_of_inf_ker h).trans hP.2⟩

theorem map_subtype_conj_smul {H : Subgroup G} (c : H) (K : Subgroup H) :
    (MulAut.conj c • K).map H.subtype =
      (K.map H.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · refine ⟨c⁻¹ * y * c, ?_, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hy
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨c * z * c⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hz
    · simp [MulAut.conj_apply]

variable [Finite G]

theorem inf_ker_eq_bot {f : G →* G'} (hker : Odd (Nat.card f.ker)) {P : Subgroup G}
    (hP : IsPGroup 2 P) : P ⊓ f.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  apply Subgroup.inf_eq_bot_of_coprime
  rw [hk]
  exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hker)

theorem exists_lift {f : G →* G'} (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    {P' : Subgroup G'} (hP' : IsPGroup 2 P') {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRP : R.map f ≤ P') : ∃ P : Subgroup G, R ≤ P ∧ P.map f = P' ∧ P ⊓ f.ker = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := P'.comap f with hC
  have hRC : R ≤ C := Subgroup.map_le_iff_le_comap.mp hRP
  obtain ⟨S, hS⟩ := (hR.comap_subtype (K := C)).exists_le_sylow
  let ψ : ↥C →* ↥P' := (f.comp C.subtype).codRestrict P' (fun c => c.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hS' : ((S.mapSurjective hψ : Sylow 2 ↥P') : Subgroup ↥P') = ⊤ :=
    ((S.mapSurjective hψ).is_maximal' (hP'.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at hS'
  have hPp : IsPGroup 2 ((S : Subgroup C).map C.subtype) := S.isPGroup'.map _
  refine ⟨(S : Subgroup C).map C.subtype, fun x hx => ⟨⟨x, hRC hx⟩, hS hx, rfl⟩, ?_,
    inf_ker_eq_bot hker hPp⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    exact s.2
  · intro y hy
    have hy' : (⟨y, hy⟩ : ↥P') ∈ (S : Subgroup C).map ψ := hS' ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsy⟩ := hy'
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsy⟩

theorem exists_conj_of_map_eq {f : G →* G'} (hker : Odd (Nat.card f.ker)) {P₁ P₂ : Subgroup G}
    (h₁ : IsPGroup 2 P₁) (h₂ : IsPGroup 2 P₂) (h : P₁.map f = P₂.map f) :
    ∃ k ∈ f.ker, P₂ = P₁.map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := (P₁.map f).comap f with hC
  have hP₁C : P₁ ≤ C := Subgroup.le_comap_map f P₁
  have hP₂C : P₂ ≤ C := by rw [hC, h]; exact Subgroup.le_comap_map f P₂
  have key : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ C → P.map f = P₁.map f →
      ∃ S : Sylow 2 ↥C, (S : Subgroup ↥C) = P.subgroupOf C := by
    intro P hP hPC hPf
    obtain ⟨S, hS⟩ := (hP.comap_subtype (K := C)).exists_le_sylow
    refine ⟨S, le_antisymm ?_ hS⟩
    have hSG : IsPGroup 2 ((S : Subgroup C).map C.subtype) := S.isPGroup'.map _
    haveI : Finite ↥(P.map f) := Finite.of_surjective _ (f.subgroupMap_surjective P)
    have hle : ((S : Subgroup C).map C.subtype).map f ≤ P.map f := by
      rw [hPf]
      rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      exact s.2
    have hcard : Nat.card (S : Subgroup C) ≤ Nat.card (P.subgroupOf C) := by
      calc Nat.card (S : Subgroup C)
          = Nat.card ((S : Subgroup C).map C.subtype) :=
            (Subgroup.card_map_of_injective C.subtype_injective).symm
        _ = Nat.card (((S : Subgroup C).map C.subtype).map f) :=
            (card_map_of_inf_ker (inf_ker_eq_bot hker hSG)).symm
        _ ≤ Nat.card (P.map f) := Subgroup.card_le_of_le hle
        _ = Nat.card P := card_map_of_inf_ker (inf_ker_eq_bot hker hP)
        _ = Nat.card (P.subgroupOf C) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv).symm
    exact (Subgroup.eq_of_le_of_card_ge hS hcard).ge
  obtain ⟨S₁, hS₁⟩ := key P₁ h₁ hP₁C rfl
  obtain ⟨S₂, hS₂⟩ := key P₂ h₂ hP₂C h.symm
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥C) S₁ S₂
  have hc' : P₂ = P₁.map (MulAut.conj (c : G)).toMonoidHom := by
    have e1 : P₂ = (P₂.subgroupOf C).map C.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hP₂C).symm
    have e2 : P₁ = (P₁.subgroupOf C).map C.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hP₁C).symm
    rw [e1, ← hS₂, ← hc, Sylow.coe_subgroup_smul, map_subtype_conj_smul, hS₁, ← e2]
  obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P₁, f p = f c := c.2
  refine ⟨c * p⁻¹, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hpc, mul_inv_cancel]
  · rw [hc']
    have hP₁p : P₁.map (MulAut.conj p).toMonoidHom = P₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hp)
    conv_rhs => rw [← hP₁p, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

theorem lift_rtg {f : G →* G'} (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    {U : Subgroup G} (hU : IsPGroup 2 U) {V' : Subgroup G'}
    (h : Relation.ReflTransGen E8Adj (U.map f) V') :
    ∃ V : Subgroup G, IsPGroup 2 V ∧ V.map f = V' ∧ Relation.ReflTransGen E8Adj U V := by
  induction h with
  | refl => exact ⟨U, hU, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hstep ih =>
    obtain ⟨W, hW, hWf, hUW⟩ := ih
    obtain ⟨E', hE', hE'8, hbE', hcE', hb4, hc4⟩ := hstep
    obtain ⟨E, hWE, hEf, hEker⟩ :=
      exists_lift hf hker (isPGroup_of_isElemAbelian hE') hW (hWf ▸ hbE')
    have hEab : IsElemAbelian 2 E := isElemAbelian_of_map hEker (hEf ▸ hE')
    have hcp : IsPGroup 2 (E ⊓ c.comap f : Subgroup G) :=
      (isPGroup_of_isElemAbelian hEab).to_le inf_le_left
    have hcmap : (E ⊓ c.comap f).map f = c := by
      apply le_antisymm
      · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le f _)
      · intro y hy
        have hy' : y ∈ E.map f := hEf ▸ hcE' hy
        obtain ⟨x, hx, rfl⟩ := hy'
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨E ⊓ c.comap f, hcp, hcmap,
      hUW.tail ⟨E, hEab, ?_, hWE, inf_le_left, ?_, ?_⟩⟩
    · rw [← card_map_of_inf_ker hEker, hEf]
      exact hE'8
    · rw [← card_map_of_inf_ker (inf_ker_eq_bot hker hW), hWf]
      exact hb4
    · rw [← card_map_of_inf_ker (inf_ker_eq_bot hker hcp), hcmap]
      exact hc4

theorem exists_conj_rtg_of_quot {f : G →* G'} (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker))
    (hconn : ∀ U V : Subgroup G', IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V)
    {U V : Subgroup G} (hU : IsFour U) (hV : IsFour V) :
    ∃ k ∈ f.ker, Relation.ReflTransGen E8Adj U (V.map (MulAut.conj k).toMonoidHom) := by
  have hUp := isPGroup_of_isElemAbelian hU.1
  have hVp := isPGroup_of_isElemAbelian hV.1
  obtain ⟨W, hW, hWf, hUW⟩ := lift_rtg hf hker hUp
    (hconn _ _ (isFour_map (inf_ker_eq_bot hker hUp) hU) (isFour_map (inf_ker_eq_bot hker hVp) hV))
  obtain ⟨k, hk, hWk⟩ := exists_conj_of_map_eq hker hVp hW hWf.symm
  exact ⟨k, hk, hWk ▸ hUW⟩

theorem exists_e8_of_quot {f : G →* G'} (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker))
    (hE8 : ∀ U : Subgroup G', IsFour U →
      ∃ E : Subgroup G', IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E)
    {U : Subgroup G} (hU : IsFour U) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E := by
  have hUp := isPGroup_of_isElemAbelian hU.1
  obtain ⟨E', hE', hE'8, hUE'⟩ := hE8 _ (isFour_map (inf_ker_eq_bot hker hUp) hU)
  obtain ⟨E, hUE, hEf, hEker⟩ := exists_lift hf hker (isPGroup_of_isElemAbelian hE') hUp hUE'
  refine ⟨E, isElemAbelian_of_map hEker (hEf ▸ hE'), ?_, hUE⟩
  rw [← card_map_of_inf_ker hEker, hEf]
  exact hE'8

theorem exists_four_mem_of_quot {f : G →* G'} (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker))
    (hinv : ∀ x : G', orderOf x = 2 → ∃ U : Subgroup G', IsFour U ∧ x ∈ U)
    {x : G} (hx : orderOf x = 2) : ∃ U : Subgroup G, IsFour U ∧ x ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; rfl)
  have hinf := inf_ker_eq_bot hker hxp
  have hfx : orderOf (f x) = 2 := by
    rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, card_map_of_inf_ker hinf, Nat.card_zpowers,
      hx]
  obtain ⟨U', hU', hxU'⟩ := hinv _ hfx
  obtain ⟨U, hxU, hUf, hUker⟩ := exists_lift hf hker (isPGroup_of_isElemAbelian hU'.1) hxp
    (by rw [MonoidHom.map_zpowers]; exact (Subgroup.zpowers_le).2 hxU')
  exact ⟨U, isFour_of_map hUker (hUf ▸ hU'), hxU (Subgroup.mem_zpowers x)⟩

theorem exists_four_of_quot {f : G →* G'} (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) (hex : ∃ U : Subgroup G', IsFour U) :
    ∃ U : Subgroup G, IsFour U := by
  obtain ⟨U', hU'⟩ := hex
  obtain ⟨U, -, hUf, hUker⟩ := exists_lift hf hker (isPGroup_of_isElemAbelian hU'.1)
    IsPGroup.of_bot (by simp)
  exact ⟨U, isFour_of_map hUker (hUf ▸ hU')⟩

end Lift


section Prod

theorem isElemAbelian_zpowers {G : Type*} [Group G] {a : G} (ha : orderOf a = 2) :
    IsElemAbelian 2 (zpowers a) :=
  isElemAbelian_of_sq fun y hy => orderOf_dvd_iff_pow_eq_one.mp (by
    have := Subgroup.orderOf_dvd_natCard (zpowers a) hy
    rwa [Nat.card_zpowers, ha] at this)

variable {A B : Type*} [Group A] [Group B]

theorem isElemAbelian_prod {H : Subgroup A} {K : Subgroup B} (hH : IsElemAbelian 2 H)
    (hK : IsElemAbelian 2 K) : IsElemAbelian 2 (H.prod K) :=
  isElemAbelian_of_sq fun x hx =>
    Prod.ext (by rw [Prod.pow_fst, Prod.fst_one]; exact hH.2 _ hx.1)
      (by rw [Prod.pow_snd, Prod.snd_one]; exact hK.2 _ hx.2)

theorem card_prod_eq (H : Subgroup A) (K : Subgroup B) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (H.prodEquiv K).toEquiv, Nat.card_prod]

theorem isFour_prod_bot {U : Subgroup A} (hU : IsFour U) : IsFour (U.prod (⊥ : Subgroup B)) :=
  ⟨isElemAbelian_prod hU.1 (CFSG.SectionRank.isElemAbelian_bot 2), by
    rw [card_prod_eq, hU.2, Subgroup.card_bot, mul_one]⟩

theorem e8Adj_prod_bot {U V : Subgroup A} (h : E8Adj U V) :
    E8Adj (U.prod (⊥ : Subgroup B)) (V.prod ⊥) := by
  obtain ⟨E, hE, hE8, hUE, hVE, hU4, hV4⟩ := h
  exact ⟨E.prod ⊥, isElemAbelian_prod hE (CFSG.SectionRank.isElemAbelian_bot 2),
    by rw [card_prod_eq, Subgroup.card_bot, mul_one]; exact hE8,
    Subgroup.prod_mono hUE le_rfl, Subgroup.prod_mono hVE le_rfl,
    by rw [card_prod_eq, Subgroup.card_bot, mul_one]; exact hU4,
    by rw [card_prod_eq, Subgroup.card_bot, mul_one]; exact hV4⟩

theorem rtg_prod_bot {U V : Subgroup A} (h : Relation.ReflTransGen E8Adj U V) :
    Relation.ReflTransGen E8Adj (U.prod (⊥ : Subgroup B)) (V.prod ⊥) :=
  rtg_map_of (fun W : Subgroup A => W.prod (⊥ : Subgroup B)) (fun _ _ h => e8Adj_prod_bot h) h

variable [Finite A] [Finite B]

theorem exists_four_ge (hA3 : ∀ a : A, orderOf a = 2 → ∃ U : Subgroup A, IsFour U ∧ a ∈ U)
    (hA4 : ∃ U : Subgroup A, IsFour U) {X : Subgroup A} (hX : IsElemAbelian 2 X)
    (hX4 : Nat.card X ∣ 4) : ∃ U : Subgroup A, IsFour U ∧ X ≤ U := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at hX4
  obtain ⟨i, hi, hXi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hX4
  interval_cases i
  · obtain ⟨U, hU⟩ := hA4
    have hXb : X = ⊥ := Subgroup.eq_bot_of_card_eq X (by simpa using hXi)
    exact ⟨U, hU, hXb ▸ bot_le⟩
  · have hne : X ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hXi; norm_num at hXi
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have ha1' : (a : A) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have ha2 : orderOf (a : A) = 2 := orderOf_eq_two_of_mem hX a.2 ha1'
    have hXa : zpowers (a : A) = X := Subgroup.eq_of_le_of_card_ge
      ((Subgroup.zpowers_le).2 a.2) (by rw [hXi, Nat.card_zpowers, ha2]; norm_num)
    obtain ⟨U, hU, haU⟩ := hA3 _ ha2
    exact ⟨U, hU, hXa ▸ (Subgroup.zpowers_le).2 haU⟩
  · exact ⟨X, ⟨hX, by rw [hXi]; norm_num⟩, le_rfl⟩

theorem prod_props
    (hA1 : ∀ U : Subgroup A, IsFour U →
      ∃ E : Subgroup A, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E)
    (hA2 : ∀ U V : Subgroup A, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V)
    (hA3 : ∀ a : A, orderOf a = 2 → ∃ U : Subgroup A, IsFour U ∧ a ∈ U)
    (hA4 : ∃ U : Subgroup A, IsFour U) :
    (∀ U V : Subgroup (A × B), IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V) ∧
    (∀ U : Subgroup (A × B), IsFour U →
      ∃ E : Subgroup (A × B), IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E) ∧
    (∀ x : A × B, orderOf x = 2 → ∃ U : Subgroup (A × B), IsFour U ∧ x ∈ U) ∧
    (∃ U : Subgroup (A × B), IsFour U) := by
  have key : ∀ U : Subgroup (A × B), IsFour U → ∃ UA : Subgroup A, IsFour UA ∧
      ∃ E : Subgroup (A × B), IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E ∧
        UA.prod (⊥ : Subgroup B) ≤ E := by
    intro U hU
    set Ua := U.map (MonoidHom.fst A B) with hUa_def
    set Ub := U.map (MonoidHom.snd A B) with hUb_def
    have hUab : U ≤ Ua.prod Ub := Subgroup.le_prod_iff.mpr ⟨le_rfl, le_rfl⟩
    have hUa : IsElemAbelian 2 Ua := isElemAbelian_map' _ hU.1
    have hUb : IsElemAbelian 2 Ub := isElemAbelian_map' _ hU.1
    have hUa4 : Nat.card Ua ∣ 4 := hU.2 ▸ Subgroup.card_map_dvd U _
    by_cases hb : Ub = ⊥
    · have hle : U ≤ Ua.prod ⊥ := hb ▸ hUab
      have hcard : Nat.card (Ua.prod (⊥ : Subgroup B)) ≤ Nat.card U := by
        rw [card_prod_eq, Subgroup.card_bot, mul_one]
        exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd U _)
      have heq : U = Ua.prod ⊥ := Subgroup.eq_of_le_of_card_ge hle hcard
      have hUa4' : IsFour Ua := ⟨hUa, by
        have h := hU.2
        rw [heq, card_prod_eq, Subgroup.card_bot, mul_one] at h
        exact h⟩
      obtain ⟨EA, hEA, hEA8, hUaEA⟩ := hA1 Ua hUa4'
      exact ⟨Ua, hUa4', EA.prod ⊥, isElemAbelian_prod hEA (CFSG.SectionRank.isElemAbelian_bot 2),
        by rw [card_prod_eq, Subgroup.card_bot, mul_one]; exact hEA8,
        (le_of_eq heq).trans (Subgroup.prod_mono hUaEA le_rfl), Subgroup.prod_mono hUaEA le_rfl⟩
    · obtain ⟨UA, hUA, hUaUA⟩ := exists_four_ge hA3 hA4 hUa hUa4
      have hUb2 : 2 ≤ Nat.card Ub := by
        have h1 : 1 < Nat.card Ub := (Subgroup.one_lt_card_iff_ne_bot Ub).2 hb
        omega
      refine ⟨UA, hUA, UA.prod Ub, isElemAbelian_prod hUA.1 hUb, ?_,
        hUab.trans (Subgroup.prod_mono hUaUA le_rfl), Subgroup.prod_mono le_rfl bot_le⟩
      rw [card_prod_eq, hUA.2]
      omega
  refine ⟨fun U V hU hV => ?_, fun U hU => ?_, fun x hx => ?_, ?_⟩
  · obtain ⟨UA, hUA, E, hE, hE8, hUE, hUAE⟩ := key U hU
    obtain ⟨VA, hVA, E', hE', hE'8, hVE', hVAE'⟩ := key V hV
    have h1 : Relation.ReflTransGen E8Adj U (UA.prod ⊥) :=
      Relation.ReflTransGen.single ⟨E, hE, hE8, hUE, hUAE, hU.2, (isFour_prod_bot hUA).2⟩
    have h2 : Relation.ReflTransGen E8Adj (VA.prod ⊥) V :=
      Relation.ReflTransGen.single ⟨E', hE', hE'8, hVAE', hVE', (isFour_prod_bot hVA).2, hV.2⟩
    exact h1.trans ((rtg_prod_bot (hA2 _ _ hUA hVA)).trans h2)
  · obtain ⟨UA, -, E, hE, hE8, hUE, -⟩ := key U hU
    exact ⟨E, hE, hE8, hUE⟩
  · have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    have ha2 : x.1 ^ 2 = 1 := by
      have h := congrArg Prod.fst hx2
      rwa [Prod.pow_fst, Prod.fst_one] at h
    have hb2 : x.2 ^ 2 = 1 := by
      have h := congrArg Prod.snd hx2
      rwa [Prod.pow_snd, Prod.snd_one] at h
    by_cases hb : x.2 = 1
    · have ha1 : x.1 ≠ 1 := fun h => by
        have h1 : x = 1 := Prod.ext h hb
        rw [h1, orderOf_one] at hx
        norm_num at hx
      obtain ⟨U, hU, haU⟩ := hA3 x.1 (orderOf_eq_prime ha2 ha1)
      exact ⟨U.prod ⊥, isFour_prod_bot hU,
        Subgroup.mem_prod.mpr ⟨haU, by rw [hb]; exact Subgroup.one_mem _⟩⟩
    · have hbo : orderOf x.2 = 2 := orderOf_eq_prime hb2 hb
      obtain ⟨a, hao, hxa⟩ : ∃ a : A, orderOf a = 2 ∧ x.1 ∈ zpowers a := by
        by_cases ha : x.1 = 1
        · obtain ⟨U, hU⟩ := hA4
          have hne : U ≠ ⊥ := fun h => by
            have h' := hU.2
            rw [h, Subgroup.card_bot] at h'
            norm_num at h'
          obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
          refine ⟨a, orderOf_eq_two_of_mem hU.1 a.2 (fun h => ha1 (Subtype.ext h)), ?_⟩
          rw [ha]
          exact Subgroup.one_mem _
        · exact ⟨x.1, orderOf_eq_prime ha2 ha, Subgroup.mem_zpowers _⟩
      refine ⟨(zpowers a).prod (zpowers x.2),
        ⟨isElemAbelian_prod (isElemAbelian_zpowers hao) (isElemAbelian_zpowers hbo), ?_⟩,
        Subgroup.mem_prod.mpr ⟨hxa, Subgroup.mem_zpowers _⟩⟩
      rw [card_prod_eq, Nat.card_zpowers, Nat.card_zpowers, hao, hbo]
  · obtain ⟨UA, hUA⟩ := hA4
    exact ⟨UA.prod ⊥, isFour_prod_bot hUA⟩

end Prod

end Groups

section Covers

open CFSG.Open

open scoped Pointwise

section Conj

variable {G : Type*} [Group G]

theorem map_conj_map_conj (a b : G) (U : Subgroup G) :
    (U.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      U.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (U : Subgroup G) : U.map (MulAut.conj (1 : G)).toMonoidHom = U := by
  ext x
  simp [MulAut.conj_apply]

theorem map_conj_inv_map_conj (a : G) (U : Subgroup G) :
    (U.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = U := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one']

theorem map_conj_map_conj_inv (a : G) (U : Subgroup G) :
    (U.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = U := by
  rw [map_conj_map_conj, mul_inv_cancel, map_conj_one']

theorem e8Adj_map_of_injective {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    {U V : Subgroup G} (h : E8Adj U V) : E8Adj (U.map f) (V.map f) := by
  obtain ⟨E, hE, hE8, hUE, hVE, hU4, hV4⟩ := h
  exact ⟨E.map f, isElemAbelian_map' f hE, by rw [Subgroup.card_map_of_injective hf]; exact hE8,
    Subgroup.map_mono hUE, Subgroup.map_mono hVE,
    by rw [Subgroup.card_map_of_injective hf]; exact hU4,
    by rw [Subgroup.card_map_of_injective hf]; exact hV4⟩

theorem rtg_map_of_injective {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    {U V : Subgroup G} (h : Relation.ReflTransGen E8Adj U V) :
    Relation.ReflTransGen E8Adj (U.map f) (V.map f) :=
  rtg_map_of (fun W : Subgroup G => W.map f) (fun _ _ h => e8Adj_map_of_injective f hf h) h

theorem rtg_conj (g : G) {U V : Subgroup G} (h : Relation.ReflTransGen E8Adj U V) :
    Relation.ReflTransGen E8Adj (U.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom) :=
  rtg_map_of_injective _ (MulAut.conj g).injective h

theorem isFour_map_of_injective {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    {U : Subgroup G} (hU : IsFour U) : IsFour (U.map f) :=
  ⟨isElemAbelian_map' f hU.1, by rw [Subgroup.card_map_of_injective hf]; exact hU.2⟩

theorem isFour_conj (g : G) {U : Subgroup G} (hU : IsFour U) :
    IsFour (U.map (MulAut.conj g).toMonoidHom) :=
  isFour_map_of_injective _ (MulAut.conj g).injective hU

theorem isFour_subgroupOf {U H : Subgroup G} (hU : IsFour U) (hUH : U ≤ H) :
    IsFour (U.subgroupOf H) := by
  have hcard : Nat.card (U.subgroupOf H) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv).trans hU.2
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (hU.1.2 _ hx)⟩,
    hcard⟩
  exact comm_of_isElemAbelian hU.1 a.2 b.2

@[expose] def compStab (U : Subgroup G) : Subgroup G where
  carrier := {g | Relation.ReflTransGen E8Adj U (U.map (MulAut.conj g).toMonoidHom)}
  one_mem' := by
    show Relation.ReflTransGen E8Adj U (U.map (MulAut.conj (1 : G)).toMonoidHom)
    rw [map_conj_one']
  mul_mem' := by
    intro a b ha hb
    show Relation.ReflTransGen E8Adj U (U.map (MulAut.conj (a * b)).toMonoidHom)
    have h := rtg_conj a hb
    rw [map_conj_map_conj] at h
    exact (ha : Relation.ReflTransGen E8Adj U _).trans h
  inv_mem' := by
    intro a ha
    show Relation.ReflTransGen E8Adj U (U.map (MulAut.conj a⁻¹).toMonoidHom)
    have h := rtg_conj a⁻¹ (ha : Relation.ReflTransGen E8Adj U _)
    rw [map_conj_inv_map_conj] at h
    exact rtg_symm h

theorem mem_compStab {U : Subgroup G} {g : G} :
    g ∈ compStab U ↔ Relation.ReflTransGen E8Adj U (U.map (MulAut.conj g).toMonoidHom) :=
  Iff.rfl

end Conj

section DoubleCover

variable {K : Type*} [Group K] [Finite K]

theorem exists_four_le_of_pRank {E : Subgroup K} (hE : 2 ≤ CFSG.Open.pRank 2 E) :
    ∃ W : Subgroup K, W ≤ E ∧ IsFour W := by
  obtain ⟨E', hE'E, hE', hE'c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) E
  have h4 : (2 : ℕ) ^ 2 ∣ Nat.card E' := by
    rw [hE'c]
    exact Nat.pow_dvd_pow 2 hE
  obtain ⟨W, hW, -, hWE'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := (⊥ : Subgroup K)) (by simp) h4 bot_le
  exact ⟨W, hWE'.trans hE'E, isElemAbelian_of_le hE' hWE', by rw [hW]; norm_num⟩

theorem rtg_of_doubleCover {n : ℕ} (hD : CoverSylowData n) {K : Type} [Group K] [Finite K]
    (hK : IsDoubleCoverOfAlt K n)
    (hgen : ∀ S : Sylow 2 K, (⨆ (E : Subgroup K) (_ : E ≤ (S : Subgroup K))
      (_ : IsMulCommutative E) (_ : 2 ≤ CFSG.Open.pRank 2 E), normalizer (E : Set K)) = ⊤)
    {U V : Subgroup K} (hU : IsFour U) (hV : IsFour V) : Relation.ReflTransGen E8Adj U V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hUS⟩ := (isPGroup_of_isElemAbelian hU.1).exists_le_sylow
  have hS : ∀ W W' : Subgroup K, IsFour W → IsFour W' → W ≤ S → W' ≤ S →
      Relation.ReflTransGen E8Adj W W' := by
    intro W W' hW hW' hWS hW'S
    have h := hD.connected K hK S ⟨W, hWS, hW.1, hW.2⟩ ⟨W', hW'S, hW'.1, hW'.2⟩
    exact rtg_map_of (fun X : FourSub (S : Subgroup K) => X.1)
      (fun X Y hXY => by
        obtain ⟨E, -, hE, hE8, hXE, hYE⟩ := hXY
        exact ⟨E, hE, hE8, hXE, hYE, X.2.2.2, Y.2.2.2⟩) h
  have htop : compStab U = ⊤ := by
    rw [eq_top_iff, ← hgen S]
    refine iSup_le fun E => iSup_le fun hES => iSup_le fun _ => iSup_le fun hE2 => ?_
    obtain ⟨W, hWE, hW⟩ := exists_four_le_of_pRank hE2
    intro g hg
    have hEg : E.map (MulAut.conj g).toMonoidHom = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hWg : W.map (MulAut.conj g).toMonoidHom ≤ S :=
      (Subgroup.map_mono hWE).trans (hEg.le.trans hES)
    have h1 := hS U W hU hW hUS (hWE.trans hES)
    have h2 := hS U _ hU (isFour_conj g hW) hUS hWg
    exact h2.trans (rtg_symm (rtg_conj g h1))
  obtain ⟨S', hVS'⟩ := (isPGroup_of_isElemAbelian hV.1).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S S'
  have hV' : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ ((g • S : Sylow 2 K) : Subgroup K) := hg ▸ hVS' hv
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hv'
    simpa [MulAut.smul_def, MulAut.conj_apply] using hv'
  have h1 := hS U _ hU (isFour_conj g⁻¹ hV) hUS hV'
  have h2 := rtg_conj g h1
  rw [map_conj_map_conj_inv] at h2
  have hgU : Relation.ReflTransGen E8Adj U (U.map (MulAut.conj g).toMonoidHom) :=
    mem_compStab.mp (htop ▸ Subgroup.mem_top g)
  exact hgU.trans h2

end DoubleCover


section Simple

open CFSG.DisconnectedInvolutionGraph.Helpers in
theorem commGraph_preconnected {Q : Type} [Group Q] [Finite Q]
    (hs : IsSimpleGroup Q) {n c : ℕ} (hF : GH74.GLS.Stage12.McLRec.CoverFacts n c)
    (hG : GH74.GLS.Stage12.OneClassDoubleCover Q n) :
    (disconnectedInvolutionCommutingGraph Q).Preconnected := by
  by_contra hdisc
  obtain ⟨t, -⟩ : ∃ t u : Involution Q,
      ¬ (disconnectedInvolutionCommutingGraph Q).Reachable t u := by
    simpa [SimpleGraph.Preconnected] using hdisc
  obtain ⟨h1, h2, h3⟩ := componentStabilizer_stronglyEmbedded t hdisc
  refine GH74.GLS.Stage12.McLRec.no_strongly_embedded_of_coverFacts hs hF hG
    (componentStabilizer t) ⟨h1, h2, fun g hg => ?_⟩ ?_
  · have hg' : g⁻¹ ∉ componentStabilizer t := fun h => hg (by simpa using inv_mem h)
    have heq : CFSG.conjugate (componentStabilizer t) g =
        conjugateSubgroup (componentStabilizer t) g⁻¹ := by
      ext x
      rw [GH74.GLS.Stage12.McLRec.mem_conjugate_iff]
      simp [conjugateSubgroup, MulAut.conj_apply]
    rw [heq]
    exact h3 g⁻¹ hg'
  · intro v hvM hv2 c hc
    have hreach : (disconnectedInvolutionCommutingGraph Q).Reachable t ⟨v, hv2⟩ :=
      (componentStabilizer_involution_iff t ⟨v, hv2⟩).mp hvM
    have hcv : conjugateInvolution c ⟨v, hv2⟩ = ⟨v, hv2⟩ := by
      apply Subtype.ext
      show MulAut.conj c v = v
      rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    have h4 := reachable_conjugate hreach c
    rw [hcv] at h4
    exact hreach.trans h4.symm

open CFSG.DisconnectedInvolutionGraph.Helpers in
theorem rtg_of_local {Q : Type*} [Group Q]
    (hloc : ∀ s : Q, orderOf s = 2 → ∀ U V : Subgroup Q, IsFour U → IsFour V →
      U ≤ centralizer ({s} : Set Q) → V ≤ centralizer ({s} : Set Q) →
        Relation.ReflTransGen E8Adj U V)
    (hpre : (disconnectedInvolutionCommutingGraph Q).Preconnected)
    {U V : Subgroup Q} (hU : IsFour U) (hV : IsFour V) : Relation.ReflTransGen E8Adj U V := by
  have hinv : ∀ W : Subgroup Q, IsFour W → ∃ w : Q, w ∈ W ∧ orderOf w = 2 := by
    intro W hW
    have hne : W ≠ ⊥ := fun h => by
      have h' := hW.2
      rw [h, Subgroup.card_bot] at h'
      norm_num at h'
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨w, w.2, orderOf_eq_two_of_mem hW.1 w.2 (fun h => hw1 (Subtype.ext h))⟩
  obtain ⟨u, huU, hu2⟩ := hinv U hU
  obtain ⟨v, hvV, hv2⟩ := hinv V hV
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hpre ⟨u, hu2⟩ ⟨v, hv2⟩)
  suffices h : ∀ w : Involution Q,
      Relation.ReflTransGen (disconnectedInvolutionCommutingGraph Q).Adj ⟨u, hu2⟩ w →
      ∀ W : Subgroup Q, IsFour W → W ≤ centralizer ({(w : Q)} : Set Q) →
        Relation.ReflTransGen E8Adj U W from
    h _ hr V hV (le_cen_of_isElemAbelian hV.1 hvV)
  intro w hw
  induction hw with
  | refl => exact fun W hW hWc => hloc u hu2 U W hU hW (le_cen_of_isElemAbelian hU.1 huU) hWc
  | @tail a b _ hab ih =>
    intro W hW hWc
    obtain ⟨hne, hcomm⟩ := (involutionGraph_adj_iff a b).mp hab
    have hne' : (a : Q) ≠ b := fun h => hne (Subtype.ext h)
    obtain ⟨W₀, hW₀, haW₀, hbW₀, -⟩ := exists_isFour_of_commute a.2 b.2 hne' hcomm
      (H := ⊤) (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hW₀a : W₀ ≤ centralizer ({(a : Q)} : Set Q) := le_cen_of_isElemAbelian hW₀.1 haW₀
    have hW₀b : W₀ ≤ centralizer ({(b : Q)} : Set Q) := le_cen_of_isElemAbelian hW₀.1 hbW₀
    exact (ih W₀ hW₀ hW₀a).trans (hloc b b.2 W₀ W hW₀ hW hW₀b hWc)

theorem simple_props {Q : Type} [Group Q] [Finite Q]
    (hs : IsSimpleGroup Q) {n c : ℕ} (hF : GH74.GLS.Stage12.McLRec.CoverFacts n c)
    (hG : GH74.GLS.Stage12.OneClassDoubleCover Q n) (hD : CoverSylowData n)
    (hgen : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n → ∀ S : Sylow 2 K,
      (⨆ (E : Subgroup K) (_ : E ≤ (S : Subgroup K)) (_ : IsMulCommutative E)
        (_ : 2 ≤ CFSG.Open.pRank 2 E), normalizer (E : Set K)) = ⊤)
    (hcov : ∀ s : Q, orderOf s = 2 → IsDoubleCoverOfAlt ↥(centralizer ({s} : Set Q)) n) :
    (∀ U : Subgroup Q, IsFour U →
      ∃ E : Subgroup Q, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E) ∧
    (∀ U V : Subgroup Q, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V) ∧
    (∀ a : Q, orderOf a = 2 → ∃ U : Subgroup Q, IsFour U ∧ a ∈ U) ∧
    (∃ U : Subgroup Q, IsFour U) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ W : Subgroup Q, IsFour W → ∃ w : Q, w ∈ W ∧ orderOf w = 2 := by
    intro W hW
    have hne : W ≠ ⊥ := fun h => by
      have h' := hW.2
      rw [h, Subgroup.card_bot] at h'
      norm_num at h'
    obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨w, w.2, orderOf_eq_two_of_mem hW.1 w.2 (fun h => hw1 (Subtype.ext h))⟩
  have hloc : ∀ s : Q, orderOf s = 2 → ∀ U V : Subgroup Q, IsFour U → IsFour V →
      U ≤ centralizer ({s} : Set Q) → V ≤ centralizer ({s} : Set Q) →
        Relation.ReflTransGen E8Adj U V := by
    intro s hs2 U V hU hV hUc hVc
    have h := rtg_of_doubleCover hD (hcov s hs2) (hgen _ (hcov s hs2))
      (isFour_subgroupOf hU hUc) (isFour_subgroupOf hV hVc)
    have h' := rtg_map_of_injective (centralizer ({s} : Set Q)).subtype
      (centralizer ({s} : Set Q)).subtype_injective h
    rwa [Subgroup.map_subgroupOf_eq_of_le hUc, Subgroup.map_subgroupOf_eq_of_le hVc] at h'
  have hA3 : ∀ a : Q, orderOf a = 2 → ∃ U : Subgroup Q, IsFour U ∧ a ∈ U := by
    intro a ha
    obtain ⟨u, hu2, hunc⟩ := hF.exists_noncentral _ (hcov a ha)
    have hu1 : (u : Q) ≠ 1 := fun h => hunc (by
      have : u = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _)
    have huo : orderOf (u : Q) = 2 := orderOf_eq_prime (by
      have := congrArg Subtype.val hu2
      simpa using this) hu1
    have hau : a ≠ (u : Q) := by
      intro h
      apply hunc
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : Q) * u = u * g
      rw [← h]
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hcomm : a * u = u * a := (Subgroup.mem_centralizer_singleton_iff.mp u.2).symm
    obtain ⟨U, hU, haU, -, -⟩ := exists_isFour_of_commute ha huo hau hcomm
      (H := ⊤) (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact ⟨U, hU, haU⟩
  refine ⟨fun U hU => ?_,
    fun U V hU hV => rtg_of_local hloc (commGraph_preconnected hs hF hG) hU hV, hA3, ?_⟩
  · obtain ⟨s, hsU, hs2⟩ := hinv U hU
    have hUc := le_cen_of_isElemAbelian hU.1 hsU
    set C := centralizer ({s} : Set Q)
    have hU' := isFour_subgroupOf hU hUc
    obtain ⟨S, hS⟩ := (isPGroup_of_isElemAbelian hU'.1).exists_le_sylow
    obtain ⟨E, -, hE, hE8, hUE⟩ := hD.four_in_E8 _ (hcov s hs2) S _ hS hU'.1 hU'.2
    refine ⟨E.map C.subtype, isElemAbelian_map' _ hE,
      by rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hE8, ?_⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hUc]
    exact Subgroup.map_mono hUE
  · obtain ⟨z, hz, -, -⟩ := hG
    obtain ⟨U, hU, -⟩ := hA3 z hz.1
    exact ⟨U, hU⟩

end Simple

end Covers

section Sporadic

open CFSG.Open

theorem thompsonJ_le' {K : Type*} [Group K] (S : Subgroup K) :
    SignalizerFunctorTheorem.Glauberman.thompsonJ 2 S ≤ S :=
  sSup_le fun _ hE => hE.1

theorem mcl_props
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.McL) :
    (∀ U : Subgroup Q, IsFour U →
      ∃ E : Subgroup Q, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E) ∧
    (∀ U V : Subgroup Q, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V) ∧
    (∀ a : Q, orderOf a = 2 → ∃ U : Subgroup Q, IsFour U ∧ a ∈ U) ∧
    (∃ U : Subgroup Q, IsFour U) := by
  have hs : IsSimpleGroup Q :=
    @MulEquiv.isSimpleGroup Q _ Blueprint.NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  have hcov : ∀ s : Q, orderOf s = 2 → IsDoubleCoverOfAlt ↥(centralizer ({s} : Set Q)) 8 :=
    fun s hs2 => CFSG.EvenSporadicStandard.McLStd.isDoubleCoverOfAlt_mcl ⟨e⟩ hs2
  have hcard : Nat.card Q = 898128000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hcard]; norm_num)
  have hnab : ∃ a b : Q, a * b ≠ b * a :=
    GH74.GLS.Stage2.Bender.Thm1.LyMult.exists_noncomm_of_simple (by rw [hcard]; norm_num)
  obtain ⟨hzc, hone⟩ :=
    CFSG.Sporadic.Recognition.JankoWong.isCentralInvolution_and_oneClass_of_doubleCover hs hnab hz
      (hcov z hz)
  have hG : GH74.GLS.Stage12.OneClassDoubleCover Q 8 := ⟨z, hzc, hone, hcov z hz⟩
  refine simple_props hs GH74.GLS.Stage12.McLRec.coverFacts_eight hG
    coverSylowData_eight_of_certificate ?_ hcov
  intro K _ _ hK S
  apply eq_top_iff.mpr
  rw [← normalizers_generate_eight_of_certificate hK S]
  refine iSup_le fun E => iSup_le fun hEJ => iSup_le fun hEab => iSup_le fun hE2 => ?_
  exact le_iSup_of_le E (le_iSup_of_le (hEJ.trans (thompsonJ_le' _))
    (le_iSup_of_le hEab (le_iSup_of_le hE2 le_rfl)))

theorem ly_props
    {Q : Type} [Group Q] [Finite Q] (e : Q ≃* Blueprint.NativeSporadic.Ly) :
    (∀ U : Subgroup Q, IsFour U →
      ∃ E : Subgroup Q, IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E) ∧
    (∀ U V : Subgroup Q, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V) ∧
    (∀ a : Q, orderOf a = 2 → ∃ U : Subgroup Q, IsFour U ∧ a ∈ U) ∧
    (∃ U : Subgroup Q, IsFour U) := by
  have hs : IsSimpleGroup Q :=
    @MulEquiv.isSimpleGroup Q _ Blueprint.NativeSporadic.Ly _ CFSG.Sporadic.Ly.isSimpleGroup_Ly e
  have hcov : ∀ s : Q, orderOf s = 2 → IsDoubleCoverOfAlt ↥(centralizer ({s} : Set Q)) 11 :=
    fun s hs2 => CFSG.EvenSporadicStandard.LyStd.isDoubleCoverOfAlt_ly ⟨e⟩ hs2
  exact simple_props hs CFSG.Sporadic.Recognition.LyonsSims.coverFacts_eleven
    (GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly ⟨e⟩)
    coverSylowData_eleven_of_certificate
    (fun K _ _ hK S => normalizers_generate_eleven_of_certificate hK S) hcov

end Sporadic

theorem exists_prod_quot
    {X : Type} [Group X] [Finite X] {n : ℕ} {H L₁ : Subgroup X} (hL₁ : Sec6MComp X n H L₁) :
    ∃ (A B : Type) (_ : Group A) (_ : Group B) (_ : Finite A) (_ : Finite B)
      (φ : ↥(Sec6M X n H) →* A × B),
      IsSec6MType n A ∧ Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup ↥H := pPrimeCore 2 ↥H with hN
  set π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N with hπ
  have hMH : Sec6M X n H ≤ H := sSup_le fun L hL => hL.1.1.1
  set Lt : Subgroup X → Subgroup (↥H ⧸ N) := fun L => (L.subgroupOf H).map π with hLt
  set At := Lt L₁ with hAt_def
  set Bt := ⨆ (L : Subgroup X) (_ : Sec6MComp X n H L) (_ : L ≠ L₁), Lt L with hBt_def
  have hpc : ∀ L, Sec6MComp X n H L → IsPComponent 2 (L.subgroupOf H) := fun L hL => hL.1.1.2
  have hBt : Bt ≤ centralizer (At : Set (↥H ⧸ N)) := by
    refine iSup_le fun L => iSup_le fun hL => iSup_le fun hne => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hne' : L₁.subgroupOf H ≠ L.subgroupOf H := fun h => hne (by
      have h' := congrArg (Subgroup.map H.subtype) h
      rw [Subgroup.map_subgroupOf_eq_of_le hL₁.1.1.1,
        Subgroup.map_subgroupOf_eq_of_le hL.1.1.1] at h'
      exact h'.symm)
    exact (commute_of_mem_map_of_isPComponent (hpc L₁ hL₁) (hpc L hL) hne' hx hy).eq
  have hcomm : ∀ x ∈ At, ∀ y ∈ Bt, Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hBt hy)) x hx
  have hsub : (L₁.subgroupOf H).IsSubnormal := (hpc L₁ hL₁).choose_spec.2.1
  obtain ⟨e₁⟩ := nonempty_quot_pPrimeCore_mulEquiv_map hsub
  let f : ↥L₁ ≃* ↥(L₁.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hL₁.1.1.1).symm
  let e₂ : (↥L₁ ⧸ pPrimeCore 2 ↥L₁) ≃* (↥(L₁.subgroupOf H) ⧸ pPrimeCore 2 ↥(L₁.subgroupOf H)) :=
    QuotientGroup.congr _ _ f (pPrimeCore_map_iso 2 f)
  have hAtype : IsSec6MType n ↥At := by
    rcases hL₁.2 with ⟨h8, ⟨g⟩⟩ | ⟨h11, ⟨g⟩⟩
    · exact Or.inl ⟨h8, ⟨(e₂.trans e₁).symm.trans g⟩⟩
    · exact Or.inr ⟨h11, ⟨(e₂.trans e₁).symm.trans g⟩⟩
  have hcen : center ↥At = ⊥ := mcLLyCenterFree ↥At (hAtype.imp And.right And.right)
  have hdisj : At ⊓ Bt = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxc : (⟨x, hxA⟩ : ↥At) ∈ center ↥At := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 x hxB).eq
    rw [hcen, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  let ψ : ↥At × ↥Bt →* ↥H ⧸ N :=
    MonoidHom.noncommCoprod At.subtype Bt.subtype (fun a b => hcomm a a.2 b b.2)
  have hψinj : Function.Injective ψ := (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨At.subtype_injective, Bt.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype]
      exact disjoint_iff.mpr hdisj⟩
  have hψrange : ψ.range = At ⊔ Bt :=
    (MonoidHom.noncommCoprod_range _ _ _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  let φ₀ : ↥(Sec6M X n H) →* ↥H ⧸ N := π.comp (Subgroup.inclusion hMH)
  have hrange : φ₀.range = At ⊔ Bt := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have hLle : ∀ L, Sec6MComp X n H L → Lt L ≤ At ⊔ Bt := by
        intro L hL
        by_cases hLL : L = L₁
        · rw [hLL]
          exact le_sup_left
        · exact le_sup_of_le_right
            (le_iSup_of_le L (le_iSup_of_le hL (le_iSup_of_le hLL le_rfl)))
      have hMT : Sec6M X n H ≤ ((At ⊔ Bt).comap π).map H.subtype := by
        refine sSup_le fun L hL => ?_
        intro l hl
        exact ⟨⟨l, hL.1.1.1 hl⟩, hLle L hL ⟨⟨l, hL.1.1.1 hl⟩, hl, rfl⟩, rfl⟩
      obtain ⟨h, hh, hhm⟩ := hMT m.2
      have him : Subgroup.inclusion hMH m = h := Subtype.ext hhm.symm
      show π (Subgroup.inclusion hMH m) ∈ At ⊔ Bt
      rw [him]
      exact hh
    · refine sup_le ?_ (iSup_le fun L => iSup_le fun hL => iSup_le fun _ => ?_)
      · rintro _ ⟨h, hh, rfl⟩
        exact ⟨⟨h, (le_sSup hL₁ : L₁ ≤ Sec6M X n H) hh⟩, rfl⟩
      · rintro _ ⟨h, hh, rfl⟩
        exact ⟨⟨h, (le_sSup hL : L ≤ Sec6M X n H) hh⟩, rfl⟩
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hker0 : Odd (Nat.card φ₀.ker) := by
    have hle : φ₀.ker.map (Subgroup.inclusion hMH) ≤ N := by
      rintro _ ⟨m, hm, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hm)
    have hcard : Nat.card (φ₀.ker.map (Subgroup.inclusion hMH)) = Nat.card φ₀.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hMH)
    exact Odd.of_dvd_nat hNodd (hcard ▸ Subgroup.card_dvd_of_le hle)
  have hmem : ∀ m, φ₀ m ∈ ψ.range := fun m => by
    rw [hψrange, ← hrange]
    exact ⟨m, rfl⟩
  let φ₁ : ↥(Sec6M X n H) →* ↥ψ.range := φ₀.codRestrict ψ.range hmem
  let e := MonoidHom.ofInjective hψinj
  refine ⟨↥At, ↥Bt, inferInstance, inferInstance, inferInstance, inferInstance,
    e.symm.toMonoidHom.comp φ₁, hAtype, ?_, ?_⟩
  · intro p
    have hp : ψ p ∈ φ₀.range := by
      rw [hrange, ← hψrange]
      exact ⟨p, rfl⟩
    obtain ⟨m, hm⟩ := hp
    refine ⟨m, ?_⟩
    show e.symm (φ₁ m) = p
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply]
    exact hm
  · have hk : (e.symm.toMonoidHom.comp φ₁).ker = φ₀.ker := by
      ext m
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hk]
    exact hker0

theorem sec6MType_props
    {n : ℕ} {Q : Type} [Group Q] [Finite Q] (hQ : IsSec6MType n Q) :
    (∀ U : Subgroup Q, IsFour U →
      ∃ E : Subgroup Q, Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E) ∧
    (∀ U V : Subgroup Q, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V) ∧
    (∀ a : Q, orderOf a = 2 → ∃ U : Subgroup Q, IsFour U ∧ a ∈ U) ∧
    (∃ U : Subgroup Q, IsFour U) := by
  rcases hQ with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact mcl_props e
  · exact ly_props e

section Sig

variable {X : Type} [Group X] [Finite X]

@[expose] def sigV (B : Subgroup X) : Subgroup X :=
  ⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)

theorem sigV_map_conj (g : X) (B : Subgroup X) :
    (sigV B).map (MulAut.conj g).toMonoidHom = sigV (B.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [← Subgroup.map_le_iff_le_comap, oddCoreOf_map_mulEquiv', cen_map]
    refine le_iSup_of_le ((MulAut.conj g) b)
      (le_iSup_of_le (Subgroup.mem_map_of_mem _ hb) (le_iSup_of_le ?_ le_rfl))
    exact fun h => hb1 ((MulAut.conj g).injective (h.trans (map_one _).symm))
  · refine iSup_le fun c => iSup_le fun hc => iSup_le fun hc1 => ?_
    obtain ⟨b, hb, rfl⟩ := hc
    have hb1 : b ≠ 1 := fun h => hc1 (by rw [h, map_one])
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
      (le_iSup_of_le b (le_iSup_of_le hb (le_iSup_of_le hb1 le_rfl)) :
        oddCoreOf (cen b) ≤ sigV B)
    rw [oddCoreOf_map_mulEquiv', cen_map] at h
    exact h

theorem map_conj_eq_of_mem_centralizer {B : Subgroup X} {c : X}
    (hc : c ∈ centralizer (B : Set X)) : B.map (MulAut.conj c).toMonoidHom = B := by
  have hcb : ∀ b ∈ B, c * b * c⁻¹ = b := fun b hb => by
    rw [← Subgroup.mem_centralizer_iff.mp hc b hb, mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    show c * b * c⁻¹ ∈ B
    rw [hcb b hb]
    exact hb
  · intro hx
    exact ⟨x, hx, hcb x hx⟩

theorem sigV_eq_W {M : Subgroup X}
    (hbal : ∀ a ∈ M, ∀ b ∈ M, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b))
    {E : Subgroup X} (hEM : E ≤ M) (hE : Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E)
    {B : Subgroup X} (hBE : B ≤ E) (hB4 : Nat.card B = 4) :
    sigV B = ⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a) :=
  (sec6_lambda2 hE hE8 (fun a ha ha1 b hb hb1 => hbal a (hEM ha) b (hEM hb)
    (orderOf_eq_two_of_mem hE ha ha1) (orderOf_eq_two_of_mem hE hb hb1)
    (comm_of_isElemAbelian hE ha hb))).2.2 B hBE hB4

theorem odd_W {M : Subgroup X}
    (hbal : ∀ a ∈ M, ∀ b ∈ M, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b))
    {E : Subgroup X} (hEM : E ≤ M) (hE : Open.IsElemAbelian 2 E) (hE8 : 8 ≤ Nat.card E) :
    Odd (Nat.card ↥(⨆ (a : X) (_ : a ∈ E) (_ : a ≠ 1), oddCoreOf (cen a))) :=
  (sec6_lambda2 hE hE8 (fun a ha ha1 b hb hb1 => hbal a (hEM ha) b (hEM hb)
    (orderOf_eq_two_of_mem hE ha ha1) (orderOf_eq_two_of_mem hE hb hb1)
    (comm_of_isElemAbelian hE ha hb))).1

theorem sigOdd_of_quot {M : Subgroup X}
    (hbal : ∀ a ∈ M, ∀ b ∈ M, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
      oddCoreOf (cen a) ⊓ cen b ≤ oddCoreOf (cen b))
    {Q : Type} [Group Q] [Finite Q] (φ : ↥M →* Q) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker))
    (hP1 : ∀ U V : Subgroup Q, IsFour U → IsFour V → Relation.ReflTransGen E8Adj U V)
    (hP2 : ∀ U : Subgroup Q, IsFour U →
      ∃ E : Subgroup Q, Open.IsElemAbelian 2 E ∧ 8 ≤ Nat.card E ∧ U ≤ E)
    (hP3 : ∀ x : Q, orderOf x = 2 → ∃ U : Subgroup Q, IsFour U ∧ x ∈ U)
    (hP4 : ∃ U : Subgroup Q, IsFour U) :
    Odd (Nat.card ↥(⨆ (b : X) (_ : b ∈ M) (_ : orderOf b = 2), oddCoreOf (cen b))) ∧
      ∀ B : Subgroup X, B ≤ M → Open.IsElemAbelian 2 B → Nat.card B = 4 →
        sigV B = ⨆ (b : X) (_ : b ∈ M) (_ : orderOf b = 2), oddCoreOf (cen b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardM : ∀ U : Subgroup ↥M, Nat.card (U.map M.subtype) = Nat.card U := fun U =>
    Subgroup.card_map_of_injective M.subtype_injective
  have hadj : ∀ U V : Subgroup ↥M, E8Adj U V →
      sigV (U.map M.subtype) = sigV (V.map M.subtype) := by
    intro U V h
    obtain ⟨E, hE, hE8, hUE, hVE, hU4, hV4⟩ := h
    have hEX := isElemAbelian_map' M.subtype hE
    have hEX8 : 8 ≤ Nat.card (E.map M.subtype) := by rw [hcardM]; exact hE8
    rw [sigV_eq_W hbal (Subgroup.map_subtype_le E) hEX hEX8 (Subgroup.map_mono hUE)
        (by rw [hcardM]; exact hU4),
      sigV_eq_W hbal (Subgroup.map_subtype_le E) hEX hEX8 (Subgroup.map_mono hVE)
        (by rw [hcardM]; exact hV4)]
  have hrtg : ∀ U V : Subgroup ↥M, Relation.ReflTransGen E8Adj U V →
      sigV (U.map M.subtype) = sigV (V.map M.subtype) := by
    intro U V h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
  have hnorm : ∀ V : Subgroup ↥M, IsFour V →
      φ.ker.map M.subtype ≤ normalizer (sigV (V.map M.subtype) : Set X) := by
    intro V hV
    obtain ⟨E, hE, hE8, hVE⟩ := exists_e8_of_quot hφ hker hP2 hV
    obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
    have h8 : 2 ^ 3 ∣ Nat.card E := by
      rw [hk]
      apply Nat.pow_dvd_pow
      by_contra hlt
      push Not at hlt
      interval_cases k <;> rw [hk] at hE8 <;> norm_num at hE8
    obtain ⟨E₀, hE₀8, hVE₀, hE₀E⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (H := V) (L := E) (by rw [hV.2]; norm_num) h8 hVE
    have hE₀ : Open.IsElemAbelian 2 E₀ := isElemAbelian_of_le hE hE₀E
    have hE₀X : Open.IsElemAbelian 2 (E₀.map M.subtype) := isElemAbelian_map' _ hE₀
    have hE₀Xc : Nat.card (E₀.map M.subtype) = 8 := by rw [hcardM, hE₀8]; norm_num
    have hNXodd : Odd (Nat.card (φ.ker.map M.subtype)) := by rw [hcardM]; exact hker
    have hE₀N : E₀.map M.subtype ≤ normalizer ((φ.ker.map M.subtype : Subgroup X) : Set X) := by
      have h1 : normalizer (φ.ker : Set ↥M) = ⊤ := Subgroup.normalizer_eq_top φ.ker
      calc E₀.map M.subtype ≤ (normalizer (φ.ker : Set ↥M)).map M.subtype := by
            rw [h1]
            exact Subgroup.map_mono le_top
        _ ≤ normalizer ((φ.ker.map M.subtype : Subgroup X) : Set X) :=
            Subgroup.le_normalizer_map _
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
      Nat.prime_two hE₀X (by rw [hE₀Xc]; norm_num) hE₀N (Nat.coprime_two_left.2 hNXodd)
    rw [← hgen]
    refine iSup₂_le fun Bh hBh => ?_
    obtain ⟨hBhE, hBhc⟩ := hBh
    have hBh4 : Nat.card Bh = 4 := by
      rw [hE₀Xc] at hBhc
      omega
    have hWB : sigV Bh = sigV (V.map M.subtype) := by
      rw [sigV_eq_W hbal (Subgroup.map_subtype_le E₀) hE₀X (by rw [hE₀Xc]) hBhE hBh4,
        sigV_eq_W hbal (Subgroup.map_subtype_le E₀) hE₀X (by rw [hE₀Xc])
          (Subgroup.map_mono hVE₀) (by rw [hcardM]; exact hV.2)]
    intro c hc
    have hcB : Bh.map (MulAut.conj c).toMonoidHom = Bh :=
      map_conj_eq_of_mem_centralizer (Subgroup.mem_inf.mp hc).2
    rw [← hWB]
    apply mem_normalizer_of_map_conj_eq
    rw [sigV_map_conj, hcB]
  have hconst : ∀ U V : Subgroup ↥M, IsFour U → IsFour V →
      sigV (U.map M.subtype) = sigV (V.map M.subtype) := by
    intro U V hU hV
    obtain ⟨k, hk, hpath⟩ := exists_conj_rtg_of_quot hφ hker hP1 hU hV
    rw [hrtg _ _ hpath]
    have hmapk : (V.map (MulAut.conj k).toMonoidHom).map M.subtype =
        (V.map M.subtype).map (MulAut.conj (k : X)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hmapk, ← sigV_map_conj]
    exact map_conj_eq_of_mem_normalizer (hnorm V hV (Subgroup.mem_map_of_mem _ hk))
  obtain ⟨F₀, hF₀⟩ := exists_four_of_quot hφ hker hP4
  have hB : ∀ B : Subgroup X, B ≤ M → Open.IsElemAbelian 2 B → Nat.card B = 4 →
      sigV B = sigV (F₀.map M.subtype) := by
    intro B hBM hB hB4
    have hF : IsFour (B.subgroupOf M) := isFour_subgroupOf ⟨hB, hB4⟩ hBM
    have h := hconst _ _ hF hF₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hBM] at h
  have hsig : (⨆ (b : X) (_ : b ∈ M) (_ : orderOf b = 2), oddCoreOf (cen b)) =
      sigV (F₀.map M.subtype) := by
    apply le_antisymm
    · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb2 => ?_
      have hb2' : orderOf (⟨b, hb⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hb2
      obtain ⟨F, hF, hbF⟩ := exists_four_mem_of_quot hφ hker hP3 hb2'
      have hb1 : b ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hb2
        norm_num at hb2
      have hle : oddCoreOf (cen b) ≤ sigV (F.map M.subtype) :=
        le_iSup_of_le b (le_iSup_of_le ⟨⟨b, hb⟩, hbF, rfl⟩ (le_iSup_of_le hb1 le_rfl))
      rw [hconst _ _ hF hF₀] at hle
      exact hle
    · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      have hbM : b ∈ M := Subgroup.map_subtype_le F₀ hb
      exact le_iSup_of_le b (le_iSup_of_le hbM
        (le_iSup_of_le (orderOf_eq_two_of_mem (isElemAbelian_map' _ hF₀.1) hb hb1) le_rfl))
  refine ⟨?_, fun B' hBM hB' hB4 => (hB B' hBM hB' hB4).trans hsig.symm⟩
  rw [hsig]
  obtain ⟨E, hE, hE8, hF₀E⟩ := exists_e8_of_quot hφ hker hP2 hF₀
  have hEX := isElemAbelian_map' M.subtype hE
  have hEX8 : 8 ≤ Nat.card (E.map M.subtype) := by rw [hcardM]; exact hE8
  rw [sigV_eq_W hbal (Subgroup.map_subtype_le E) hEX hEX8 (Subgroup.map_mono hF₀E)
    (by rw [hcardM]; exact hF₀.2)]
  exact odd_W hbal (Subgroup.map_subtype_le E) hEX hEX8

theorem sigOdd_core
    {n : ℕ} {t : X} (hhas : ∃ L, Sec6MComp X n (cen t) L) (hΛ1 : Sec6Lambda1At X n t) :
    Odd (Nat.card ↥(sec6Sig X n t)) ∧
      ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → Open.IsElemAbelian 2 B → Nat.card B = 4 →
        sigV B = sec6Sig X n t := by
  obtain ⟨L₁, hL₁⟩ := hhas
  obtain ⟨A, B, _, _, _, _, φ, hA, hφ, hker⟩ := exists_prod_quot hL₁
  obtain ⟨hA1, hA2, hA3, hA4⟩ := sec6MType_props hA
  obtain ⟨hP1, hP2, hP3, hP4⟩ := prod_props (B := B) hA1 hA2 hA3 hA4
  exact sigOdd_of_quot hΛ1 φ hφ hker hP1 hP2 hP3 hP4

end Sig

end Sec6SigOdd

theorem sec6SigOdd_of_lambda1At
    {X : Type} [Group X] [Finite X] {n : ℕ} {t : X}
    (hS : Sec6Setting X n t) (hK : Sec6Lemma51 X n) (hΛ1 : Sec6Lambda1At X n t) :
    Odd (Nat.card ↥(sec6Sig X n t)) ∧
      ∀ B : Subgroup X, B ≤ Sec6M X n (cen t) → CFSG.Open.IsElemAbelian 2 B → Nat.card B = 4 →
        (⨆ (b : X) (_ : b ∈ B) (_ : b ≠ 1), oddCoreOf (cen b)) = sec6Sig X n t :=
  Sec6SigOdd.sigOdd_core hS.choice.hasM hΛ1

end CFSG.OddStandard.Solomon75
