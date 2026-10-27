module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

theorem ffIso_mem_ffImg_iff (Φ : ↥L ≃* H) {B : Subgroup G} (l : ↥L) :
    Φ l ∈ ffImg Φ.toMonoidHom B ↔ (l : G) ∈ B := by
  rw [mem_ffImg_iff]
  constructor
  · rintro ⟨l', hl', h⟩
    have h' : l' = l := Φ.injective (by simpa using h)
    simpa [h'] using hl'
  · intro hl
    exact ⟨l, hl, rfl⟩

theorem ffIso_mem_normalizer_iff (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) (l : ↥L) :
    (l : G) ∈ Subgroup.normalizer (B : Set G) ↔
      Φ l ∈ Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H) := by
  unfold ffImg
  rw [← Subgroup.mem_subgroupOf (H := Subgroup.normalizer (B : Set G)) (K := L),
    Subgroup.subgroupOf_normalizer_eq hBL, ← Subgroup.map_equiv_normalizer_eq (B.subgroupOf L) Φ,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem ffIso_commute_iff (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) (l : ↥L) :
    (∀ b ∈ B, (l : G) * b = b * (l : G)) ↔
      ∀ b' ∈ ffImg Φ.toMonoidHom B, Φ l * b' = b' * Φ l := by
  constructor
  · intro hcomm b' hb'
    obtain ⟨b, hb, rfl⟩ := mem_ffImg_iff.mp hb'
    have hlb : l * b = b * l := Subtype.ext (hcomm b hb)
    change Φ.toMonoidHom l * Φ.toMonoidHom b = Φ.toMonoidHom b * Φ.toMonoidHom l
    rw [← map_mul, ← map_mul, hlb]
  · intro hcomm b hb
    let bl : ↥L := ⟨b, hBL hb⟩
    have hbl : Φ bl ∈ ffImg Φ.toMonoidHom B := (ffIso_mem_ffImg_iff Φ bl).mpr hb
    have hconj : l * bl = bl * l := by
      apply Φ.injective
      rw [map_mul, map_mul]
      exact hcomm (Φ bl) hbl
    exact congrArg (fun x : ↥L => (x : G)) hconj

theorem ffIso_quotEquivTo (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) {F : Type} [Group F]
    (h : QuotEquivTo (Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H))
      (ffImg Φ.toMonoidHom B) F) :
    QuotEquivTo (L ⊓ Subgroup.normalizer (B : Set G)) B F := by
  obtain ⟨ψ, hψs, hψk⟩ := h
  let N : Subgroup G := L ⊓ Subgroup.normalizer (B : Set G)
  let M : Subgroup H := Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H)
  have hχmem : ∀ n : ↥N, Φ ⟨(n : G), (Subgroup.mem_inf.mp n.2).1⟩ ∈ M := by
    intro n
    exact (ffIso_mem_normalizer_iff Φ hBL ⟨(n : G), (Subgroup.mem_inf.mp n.2).1⟩).mp
      (Subgroup.mem_inf.mp n.2).2
  let χ : ↥N →* ↥M :=
    MonoidHom.mk' (fun n => ⟨Φ ⟨(n : G), (Subgroup.mem_inf.mp n.2).1⟩, hχmem n⟩)
      (fun n m => by
        apply Subtype.ext
        show Φ ⟨((n * m : ↥N) : G), (Subgroup.mem_inf.mp (n * m).2).1⟩ =
          Φ ⟨(n : G), (Subgroup.mem_inf.mp n.2).1⟩ *
            Φ ⟨(m : G), (Subgroup.mem_inf.mp m.2).1⟩
        rw [← map_mul]
        congr 1)
  have hχval : ∀ n : ↥N, (χ n : H) = Φ ⟨(n : G), (Subgroup.mem_inf.mp n.2).1⟩ :=
    fun _ => rfl
  have hχs : Function.Surjective χ := by
    intro m
    obtain ⟨l, hl⟩ := Φ.surjective (m : H)
    have hlN : (l : G) ∈ Subgroup.normalizer (B : Set G) := by
      apply (ffIso_mem_normalizer_iff Φ hBL l).mpr
      rw [hl]
      exact m.2
    refine ⟨⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlN⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hχval]
    exact (congrArg (fun y : ↥L => Φ y) (Subtype.ext rfl)).trans hl
  refine ⟨ψ.comp χ, hψs.comp hχs, ?_⟩
  apply Subgroup.ext
  intro n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change ψ (χ n) = 1 ↔ (n : G) ∈ B
  rw [← MonoidHom.mem_ker (f := ψ) (x := χ n), hψk, Subgroup.mem_subgroupOf, hχval,
    ffIso_mem_ffImg_iff]

theorem ffIso_centralizer (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (h : ∀ n : H, (∀ b' ∈ ffImg Φ.toMonoidHom B, n * b' = b' * n) →
      n ∈ ffImg Φ.toMonoidHom B) :
    L ⊓ Subgroup.centralizer (B : Set G) = B := by
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    let l : ↥L := ⟨x, hxL⟩
    have hcomm : ∀ b ∈ B, (l : G) * b = b * (l : G) := by
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 b hb).symm
    have hb' : ∀ b' ∈ ffImg Φ.toMonoidHom B, Φ l * b' = b' * Φ l :=
      (ffIso_commute_iff Φ hBL l).mp hcomm
    exact (ffIso_mem_ffImg_iff Φ l).mp (h (Φ l) hb')
  · intro b hb
    refine Subgroup.mem_inf.mpr ⟨hBL hb, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    exact (hB b hb b' hb').symm

theorem ffIso_permModule_to (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) {n : ℕ}
    (h : ∃ κ : (Fin n → ZMod 2) → H, IsPermModuleVia IsEvenVec κ (ffImg Φ.toMonoidHom B)
      (Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H)) ⊤) :
    ∃ φ : (Fin n → ZMod 2) → G,
      IsPermModuleVia IsEvenVec φ B (L ⊓ Subgroup.normalizer (B : Set G)) ⊤ := by
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun v => ((Φ.symm (κ v) : ↥L) : G), ?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    show ((Φ.symm (κ (v + w)) : ↥L) : G) =
      ((Φ.symm (κ v) : ↥L) : G) * ((Φ.symm (κ w) : ↥L) : G)
    rw [h1 v w hv hw, map_mul]
    simp
  · intro v w hv hw heq
    apply h2 v w hv hw
    apply Φ.symm.injective
    exact Subtype.ext heq
  · intro x
    constructor
    · intro hx
      let l : ↥L := ⟨x, hBL hx⟩
      have hl : Φ l ∈ ffImg Φ.toMonoidHom B := (ffIso_mem_ffImg_iff Φ l).mpr hx
      obtain ⟨v, hv, hκv⟩ := (h3 (Φ l)).mp hl
      refine ⟨v, hv, ?_⟩
      show ((Φ.symm (κ v) : ↥L) : G) = x
      rw [hκv, MulEquiv.symm_apply_apply]
    · rintro ⟨v, hv, hφv⟩
      have hκB : κ v ∈ ffImg Φ.toMonoidHom B := (h3 (κ v)).mpr ⟨v, hv, rfl⟩
      rw [← hφv]
      exact (ffIso_mem_ffImg_iff Φ (Φ.symm (κ v))).mp (by simpa using hκB)
  · intro h hh
    let l : ↥L := ⟨h, (Subgroup.mem_inf.mp hh).1⟩
    have hlM : Φ l ∈ Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H) :=
      (ffIso_mem_normalizer_iff Φ hBL l).mp (Subgroup.mem_inf.mp hh).2
    obtain ⟨σ, hσ, hσv⟩ := h4 (Φ l) hlM
    refine ⟨σ, hσ, fun v hv => ?_⟩
    have heq : (l * Φ.symm (κ v) * l⁻¹ : ↥L) = Φ.symm (κ (permVec σ v)) := by
      apply Φ.injective
      simpa [map_mul, map_inv, MulEquiv.apply_symm_apply] using hσv v hv
    simpa [l] using congrArg (fun y : ↥L => (y : G)) heq
  · intro σ hσ
    obtain ⟨h', hh'M, hσv⟩ := h5 σ hσ
    let l : ↥L := Φ.symm h'
    have hl' : Φ l = h' := MulEquiv.apply_symm_apply Φ h'
    have hlN : (l : G) ∈ Subgroup.normalizer (B : Set G) := by
      apply (ffIso_mem_normalizer_iff Φ hBL l).mpr
      rw [hl']
      exact hh'M
    refine ⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2, hlN⟩, fun v hv => ?_⟩
    have heq : (l * Φ.symm (κ v) * l⁻¹ : ↥L) = Φ.symm (κ (permVec σ v)) := by
      apply Φ.injective
      simpa [map_mul, map_inv, hl', MulEquiv.apply_symm_apply] using hσv v hv
    simpa using congrArg (fun y : ↥L => (y : G)) heq

theorem ffIso_permModule_of (Φ : ↥L ≃* H) {B : Subgroup G} (hBL : B ≤ L) {n : ℕ}
    {φ : (Fin n → ZMod 2) → G}
    (h : IsPermModuleVia IsEvenVec φ B (L ⊓ Subgroup.normalizer (B : Set G)) ⊤) :
    ∃ ψ : (Fin n → ZMod 2) → H,
      IsPermModuleVia IsEvenVec ψ (ffImg Φ.toMonoidHom B)
        (Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H)) ⊤ ∧
      ∀ v, IsEvenVec v → ∃ hv : φ v ∈ L, ψ v = Φ ⟨φ v, hv⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  classical
  let ψ : (Fin n → ZMod 2) → H := fun v => if hv : φ v ∈ L then Φ ⟨φ v, hv⟩ else 1
  have hψeven : ∀ v, IsEvenVec v → ∃ hv : φ v ∈ L, ψ v = Φ ⟨φ v, hv⟩ := by
    intro v hv
    have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
    exact ⟨hBL hvB, dif_pos (hBL hvB)⟩
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_, ?_⟩, hψeven⟩
  · dsimp only [ψ]
    intro v w hv hw
    have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
    have hwB : φ w ∈ B := (h3 (φ w)).mpr ⟨w, hw, rfl⟩
    have hvwB : φ (v + w) ∈ B := by
      rw [h1 v w hv hw]
      exact B.mul_mem hvB hwB
    rw [dif_pos (hBL hvB), dif_pos (hBL hwB), dif_pos (hBL hvwB), ← map_mul]
    congr 1
    exact Subtype.ext (h1 v w hv hw)
  · dsimp only [ψ]
    intro v w hv hw heq
    have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
    have hwB : φ w ∈ B := (h3 (φ w)).mpr ⟨w, hw, rfl⟩
    rw [dif_pos (hBL hvB), dif_pos (hBL hwB)] at heq
    exact h2 v w hv hw (congrArg (fun x : ↥L => (x : G)) (Φ.injective heq))
  · dsimp only [ψ]
    intro x
    constructor
    · intro hx
      obtain ⟨l, hlB, rfl⟩ := mem_ffImg_iff.mp hx
      obtain ⟨v, hv, hvl⟩ := (h3 (l : G)).mp hlB
      refine ⟨v, hv, ?_⟩
      have hvL : φ v ∈ L := by rw [hvl]; exact hBL hlB
      rw [dif_pos hvL]
      exact congrArg (fun y : ↥L => Φ y) (Subtype.ext hvl)
    · rintro ⟨v, hv, hψ⟩
      have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
      have hvL : φ v ∈ L := hBL hvB
      rw [dif_pos hvL] at hψ
      rw [← hψ]
      exact (ffIso_mem_ffImg_iff Φ ⟨φ v, hvL⟩).mpr hvB
  · dsimp only [ψ]
    intro h' hh'
    obtain ⟨l, hl⟩ := Φ.surjective h'
    have hlN : (l : G) ∈ Subgroup.normalizer (B : Set G) := by
      apply (ffIso_mem_normalizer_iff Φ hBL l).mpr
      rw [hl]
      exact hh'
    obtain ⟨σ, hσ, hσv⟩ := h4 (l : G) (Subgroup.mem_inf.mpr ⟨l.2, hlN⟩)
    refine ⟨σ, hσ, fun v hv => ?_⟩
    have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
    have hvL : φ v ∈ L := hBL hvB
    have hpB : φ (permVec σ v) ∈ B := by
      rw [← hσv v hv]
      exact (Subgroup.mem_normalizer_iff.mp hlN (φ v)).mp hvB
    rw [dif_pos hvL, dif_pos (hBL hpB), ← hl]
    have heq : (l * ⟨φ v, hvL⟩ * l⁻¹ : ↥L) = ⟨φ (permVec σ v), hBL hpB⟩ :=
      Subtype.ext (hσv v hv)
    simpa [map_mul, map_inv] using congrArg (fun y : ↥L => Φ y) heq
  · dsimp only [ψ]
    intro σ hσ
    obtain ⟨h, hh, hσv⟩ := h5 σ hσ
    let l : ↥L := ⟨h, (Subgroup.mem_inf.mp hh).1⟩
    have hlM : Φ l ∈ Subgroup.normalizer (ffImg Φ.toMonoidHom B : Set H) :=
      (ffIso_mem_normalizer_iff Φ hBL l).mp (Subgroup.mem_inf.mp hh).2
    refine ⟨Φ l, hlM, fun v hv => ?_⟩
    have hvB : φ v ∈ B := (h3 (φ v)).mpr ⟨v, hv, rfl⟩
    have hvL : φ v ∈ L := hBL hvB
    have hpB : φ (permVec σ v) ∈ B := by
      rw [← hσv v hv]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hh).2 (φ v)).mp hvB
    rw [dif_pos hvL, dif_pos (hBL hpB)]
    have heq : (l * ⟨φ v, hvL⟩ * l⁻¹ : ↥L) = ⟨φ (permVec σ v), hBL hpB⟩ :=
      Subtype.ext (hσv v hv)
    simpa [map_mul, map_inv] using congrArg (fun y : ↥L => Φ y) heq

end CFSG.OddStandard.SmallF3.Omega
