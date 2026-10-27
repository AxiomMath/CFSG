module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.LocalAnalysis.Replacement.ReplacementTheorem
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson

public section

namespace CFSG.Goldschmidt.G310

section ZJ

variable {X : Type*} [Group X]

theorem inf_centralizer_eq_of_mem [Finite X] {P A : Subgroup X}
    (hA : A ∈ CFSG.thompsonAbelianSubgroups P) : P ⊓ Subgroup.centralizer (A : Set X) = A := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ⟨hA.1 hx,
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.2.1) hx⟩)
  have := hA.2.1
  set B := Subgroup.closure (insert x (A : Set X)) with hB
  have hBP : B ≤ P := (Subgroup.closure_le _).mpr (Set.insert_subset hx.1 hA.1)
  have hBc : IsMulCommutative B := Subgroup.isMulCommutative_closure <|
    Set.pairwise_insert_of_symm.2
      ⟨fun a ha b hb _ => setLike_mul_comm ha hb,
        fun a ha _ => (Subgroup.mem_centralizer_iff.mp hx.2 a ha).symm⟩
  have hAB : A ≤ B := (Set.subset_insert _ _).trans Subgroup.subset_closure
  have hAB' : A = B := Subgroup.eq_of_le_of_card_ge hAB (hA.2.2 B hBP hBc)
  rw [hAB']
  exact Subgroup.subset_closure (Set.mem_insert x _)

variable [Finite X]

theorem mem_zj_iff {P : Subgroup X} {x : X} :
    x ∈ CFSG.Glauberman.ZJ P ↔ ∀ A ∈ CFSG.thompsonAbelianSubgroups P, x ∈ A := by
  constructor
  · intro hx A hA
    have hx' : x ∈ CFSG.thompsonSubgroup P ⊓
        Subgroup.centralizer (CFSG.thompsonSubgroup P : Set X) := hx
    have hJ : A ≤ CFSG.thompsonSubgroup P := le_sSup hA
    have hJP : CFSG.thompsonSubgroup P ≤ P := sSup_le fun _ hB => hB.1
    rw [← inf_centralizer_eq_of_mem hA]
    exact ⟨hJP hx'.1, Subgroup.centralizer_le hJ hx'.2⟩
  · intro hx
    obtain ⟨A₀, hA₀⟩ := CFSG.thompsonAbelianSubgroups_nonempty P
    have hJC : CFSG.thompsonSubgroup P ≤ Subgroup.centralizer ({x} : Set X) := by
      refine sSup_le fun A hA a ha => ?_
      have := hA.2.1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact setLike_mul_comm ha (hx A hA)
    refine ⟨le_sSup hA₀ (hx A₀ hA₀), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJC hy)

theorem zj_le_of_mem {P A : Subgroup X} (hA : A ∈ CFSG.thompsonAbelianSubgroups P) :
    CFSG.Glauberman.ZJ P ≤ A := fun _ hx => mem_zj_iff.mp hx A hA

theorem zj_le (P : Subgroup X) : CFSG.Glauberman.ZJ P ≤ P := by
  obtain ⟨A₀, hA₀⟩ := CFSG.thompsonAbelianSubgroups_nonempty P
  exact (zj_le_of_mem hA₀).trans hA₀.1

theorem isMulCommutative_zj (P : Subgroup X) : IsMulCommutative (CFSG.Glauberman.ZJ P) := by
  obtain ⟨A₀, hA₀⟩ := CFSG.thompsonAbelianSubgroups_nonempty P
  have := hA₀.2.1
  exact ⟨⟨fun a b => Subtype.ext (setLike_mul_comm (zj_le_of_mem hA₀ a.2)
    (zj_le_of_mem hA₀ b.2))⟩⟩

theorem zj_le_zj {P R A : Subgroup X} (hRP : R ≤ P) (hA : A ∈ CFSG.thompsonAbelianSubgroups P)
    (hAR : A ≤ R) : CFSG.Glauberman.ZJ P ≤ CFSG.Glauberman.ZJ R := by
  intro x hx
  rw [mem_zj_iff] at hx ⊢
  intro B hB
  refine hx B ⟨hB.1.trans hRP, hB.2.1, fun C hC hCc => ?_⟩
  exact (hA.2.2 C hC hCc).trans (hB.2.2 A hAR hA.2.1)

omit [Finite X] in
theorem map_mem_thompsonAbelianSubgroups {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Injective f) {P A : Subgroup X} (hA : A ∈ CFSG.thompsonAbelianSubgroups P) :
    A.map f ∈ CFSG.thompsonAbelianSubgroups (P.map f) := by
  have := hA.2.1
  refine ⟨Subgroup.map_mono hA.1, Subgroup.map_isMulCommutative A f, fun C hC hCc => ?_⟩
  have hCP : C.comap f ≤ P := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hC hx
    rwa [← hf hyx]
  have hCc' : IsMulCommutative (C.comap f) :=
    ⟨⟨fun a b => Subtype.ext (hf (by
      have := hCc.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
      simpa using congrArg Subtype.val this))⟩⟩
  have hCr : C ≤ f.range := hC.trans (Subgroup.map_le_range f P)
  have h1 : (C.comap f).map f = C := Subgroup.map_comap_eq_self hCr
  have h2 : Nat.card C = Nat.card (C.comap f) := by
    rw [← h1, Subgroup.card_map_of_injective hf, h1]
  rw [h2, Subgroup.card_map_of_injective hf]
  exact hA.2.2 _ hCP hCc'

omit [Finite X] in
theorem comap_mem_thompsonAbelianSubgroups {Y : Type*} [Group Y] [Finite Y] (f : X →* Y)
    (hf : Function.Injective f) {P : Subgroup X} {A : Subgroup Y}
    (hA : A ∈ CFSG.thompsonAbelianSubgroups (P.map f)) :
    A.comap f ∈ CFSG.thompsonAbelianSubgroups P ∧ (A.comap f).map f = A := by
  have hAr : A ≤ f.range := hA.1.trans (Subgroup.map_le_range f P)
  have h1 : (A.comap f).map f = A := Subgroup.map_comap_eq_self hAr
  refine ⟨⟨fun x hx => ?_, ?_, fun C hC hCc => ?_⟩, h1⟩
  · obtain ⟨y, hy, hyx⟩ := hA.1 hx
    rwa [← hf hyx]
  · have := hA.2.1
    exact ⟨⟨fun a b => Subtype.ext (hf (by
      have := this.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
      simpa using congrArg Subtype.val this))⟩⟩
  · have := hCc
    have h2 := hA.2.2 (C.map f) (Subgroup.map_mono hC) (Subgroup.map_isMulCommutative C f)
    rw [Subgroup.card_map_of_injective hf, ← h1, Subgroup.card_map_of_injective hf] at h2
    exact h2

theorem zj_map {Y : Type*} [Group Y] [Finite Y] (f : X →* Y) (hf : Function.Injective f)
    (P : Subgroup X) : CFSG.Glauberman.ZJ (P.map f) = (CFSG.Glauberman.ZJ P).map f := by
  ext y
  constructor
  · intro hy
    have hyP : y ∈ P.map f := zj_le _ hy
    obtain ⟨x, hxP, rfl⟩ := hyP
    refine ⟨x, mem_zj_iff.mpr fun A hA => ?_, rfl⟩
    have := mem_zj_iff.mp hy _ (map_mem_thompsonAbelianSubgroups f hf hA)
    obtain ⟨x', hx', hx'x⟩ := this
    rwa [← hf hx'x]
  · rintro ⟨x, hx, rfl⟩
    refine mem_zj_iff.mpr fun A hA => ?_
    obtain ⟨hA', hAA⟩ := comap_mem_thompsonAbelianSubgroups f hf hA
    rw [← hAA]
    exact ⟨x, mem_zj_iff.mp hx _ hA', rfl⟩

theorem normalizer_le_normalizer_zj (P : Subgroup X) :
    Subgroup.normalizer (P : Set X) ≤
      Subgroup.normalizer (CFSG.Glauberman.ZJ P : Set X) := by
  intro n hn
  have h1 : P.map (MulAut.conj n).toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn y).mp hy
    · intro hx
      refine ⟨n⁻¹ * x * n, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp ?_ |>
        fun h => by simpa using h, by simp [mul_assoc]⟩
      exact hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h2 := zj_map (MulAut.conj n).toMonoidHom (MulAut.conj n).injective P
  rw [h1] at h2
  constructor
  · intro hz
    have : n * z * n⁻¹ ∈ (CFSG.Glauberman.ZJ P).map (MulAut.conj n).toMonoidHom :=
      ⟨z, hz, by simp⟩
    rwa [← h2] at this
  · intro hz
    rw [h2] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
      exact mul_left_cancel (mul_right_cancel hwz)
    rwa [← this]

theorem zj_subgroupOf {P Y : Subgroup X} (hPY : P ≤ Y) :
    CFSG.Glauberman.ZJ (P.subgroupOf Y) = (CFSG.Glauberman.ZJ P).subgroupOf Y := by
  have h := zj_map Y.subtype Y.subtype_injective (P.subgroupOf Y)
  rw [Subgroup.map_subgroupOf_eq_of_le hPY] at h
  rw [h]
  exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _).symm

end ZJ

section Replacement

variable {X : Type*} [Group X] [Finite X]

theorem card_le_maxAbelianOrder {S : Type*} [Group S] [Finite S] (A : Subgroup S)
    (hA : IsMulCommutative A) : Nat.card A ≤ GlaubermanReplacement.maxAbelianOrder S :=
  CFSG.card_le_maxAbelianOrder_of_isMulCommutative hA

theorem exists_card_eq_maxAbelianOrder (S : Type*) [Group S] [Finite S] :
    ∃ A : Subgroup S, IsMulCommutative A ∧ Nat.card A = GlaubermanReplacement.maxAbelianOrder S :=
  CFSG.maxOrderAbelianFamily_nonempty

theorem mem_maxOrderAbelianSubgroups_iff {P : Subgroup X} {A : Subgroup P} :
    A ∈ GlaubermanReplacement.maxOrderAbelianSubgroups P ↔
      A.map P.subtype ∈ CFSG.thompsonAbelianSubgroups P := by
  rw [← CFSG.image_maxOrderAbelianFamily_eq_thompsonAbelianSubgroups]
  exact ((Subgroup.map_injective P.subtype_injective).mem_set_image).symm

theorem zj_eq_map_thompsonCenter (P : Subgroup X) :
    CFSG.Glauberman.ZJ P = (CFSG.GlaubermanReplacement.thompsonCenter P).map P.subtype :=
  CFSG.thompsonCenter_eq_ambientOrderZJ P

theorem forall_le_or_exists_le_normalizer' {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {P B : Subgroup X} (hPp : IsPGroup p P) (hBP : B ≤ P)
    (hPB : P ≤ Subgroup.normalizer (B : Set X))
    (hclass : ⁅B, B⁆ ≤ Subgroup.centralizer (B : Set X))
    (hBZ : ⁅B, B⁆ ≤ CFSG.Glauberman.ZJ P) :
    (∀ A ∈ CFSG.thompsonAbelianSubgroups P, B ≤ A) ∨
      ∃ A ∈ CFSG.thompsonAbelianSubgroups P, ¬ B ≤ A ∧
        B ≤ Subgroup.normalizer (A : Set X) := by
  set B' := B.subgroupOf P with hB'
  have hB'n : B'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mpr hPB
  have hcomm : ⁅B', B'⁆ = (⁅B, B⁆ : Subgroup X).subgroupOf P := by
    have h1 := Subgroup.map_commutator B' B' P.subtype
    rw [hB', Subgroup.map_subgroupOf_eq_of_le hBP] at h1
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hclass' : ⁅B', B'⁆ ≤ (Subgroup.center B').map B'.subtype := by
    intro x hx
    have hxB : x ∈ B' := Subgroup.commutator_le_self B' hx
    refine ⟨⟨x, hxB⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    have hx' : (x : X) ∈ ⁅B, B⁆ := by rw [hcomm] at hx; exact hx
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hclass hx') _ y.2))
  have hBZ' : ⁅B', B'⁆ ≤ CFSG.GlaubermanReplacement.thompsonCenter P := by
    intro x hx
    have hx' : (x : X) ∈ ⁅B, B⁆ := by rw [hcomm] at hx; exact hx
    have := hBZ hx'
    rw [zj_eq_map_thompsonCenter] at this
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from Subtype.ext hyx] at hy
  rcases CFSG.GlaubermanReplacement.forall_le_or_exists_le_normalizer hp hodd
      (hPp : IsPGroup p P) B' hB'n hclass' hBZ' with h | ⟨A', hA', hBA', hBN'⟩
  · left
    intro A hA
    have hA' : A.subgroupOf P ∈ CFSG.GlaubermanReplacement.maxOrderAbelianSubgroups P := by
      rw [mem_maxOrderAbelianSubgroups_iff, Subgroup.map_subgroupOf_eq_of_le hA.1]
      exact hA
    intro b hb
    exact h _ hA' (show (⟨b, hBP hb⟩ : P) ∈ B' from hb)
  · right
    refine ⟨A'.map P.subtype, mem_maxOrderAbelianSubgroups_iff.mp hA', fun hle => hBA' ?_,
      fun b hb => ?_⟩
    · intro b hb
      obtain ⟨c, hc, hcb⟩ := hle hb
      rwa [show c = b from Subtype.ext hcb] at hc
    · have hbN := hBN' (show (⟨b, hBP hb⟩ : P) ∈ B' from hb)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨_, (Subgroup.mem_normalizer_iff.mp hbN w).mp hw, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        have hwz' : (w : X) = b * z * b⁻¹ := hwz
        have hzP : z ∈ P := by
          have e : z = b⁻¹ * (w : X) * b := by rw [hwz']; group
          rw [e]
          exact P.mul_mem (P.mul_mem (P.inv_mem (hBP hb)) w.2) (hBP hb)
        refine ⟨⟨z, hzP⟩, (Subgroup.mem_normalizer_iff.mp hbN _).mpr ?_, rfl⟩
        have : (⟨b, hBP hb⟩ : P) * ⟨z, hzP⟩ * (⟨b, hBP hb⟩ : P)⁻¹ = w :=
          Subtype.ext hwz'.symm
        rw [this]
        exact hw

end Replacement

end CFSG.Goldschmidt.G310
