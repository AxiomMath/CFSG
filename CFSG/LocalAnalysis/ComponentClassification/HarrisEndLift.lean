module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools

namespace HarrisEnd

variable {X : Type} [Group X] [Finite X] (M : Subgroup X)

@[expose] def barOf (P : Subgroup X) : Subgroup (↥M ⧸ pPrimeCore 2 ↥M) :=
  (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))

@[expose] def preimageOf (A : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) : Subgroup X :=
  (A.comap (QuotientGroup.mk' (pPrimeCore 2 ↥M))).map M.subtype

variable {M}

omit [Finite X] in
theorem mem_preimageOf {A : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} {x : X} (hx : x ∈ M) :
    x ∈ preimageOf M A ↔ (QuotientGroup.mk ⟨x, hx⟩ : ↥M ⧸ pPrimeCore 2 ↥M) ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

omit [Finite X] in
theorem mk_mem_barOf {P : Subgroup X} {x : X} (hxM : x ∈ M) (hxP : x ∈ P) :
    (QuotientGroup.mk ⟨x, hxM⟩ : ↥M ⧸ pPrimeCore 2 ↥M) ∈ barOf M P :=
  ⟨⟨x, hxM⟩, hxP, rfl⟩

omit [Finite X] in
theorem mem_barOf {P : Subgroup X} {a : ↥M ⧸ pPrimeCore 2 ↥M} :
    a ∈ barOf M P ↔ ∃ x : ↥M, (x : X) ∈ P ∧ (QuotientGroup.mk x : ↥M ⧸ pPrimeCore 2 ↥M) = a := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [Finite X] in
theorem isPGroup_subgroupOf {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) :
    IsPGroup 2 (P.subgroupOf M) :=
  hP.of_equiv (subgroupOfEquivOfLe hPM).symm

theorem mk_injOn {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) {x y : X} (hx : x ∈ P)
    (hy : y ∈ P)
    (h : (QuotientGroup.mk ⟨x, hPM hx⟩ : ↥M ⧸ pPrimeCore 2 ↥M) = QuotientGroup.mk ⟨y, hPM hy⟩) :
    x = y :=
  congrArg Subtype.val (GSThmB.OddQuot.injOn_of_isPGroup (isPGroup_subgroupOf hPM hP) hx hy h)

@[expose] def barHom {P : Subgroup X} (hPM : P ≤ M) : ↥P →* ↥M ⧸ pPrimeCore 2 ↥M :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp (inclusion hPM)

theorem barHom_injective {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) :
    Function.Injective (barHom hPM) := fun x y h =>
  Subtype.ext (mk_injOn hPM hP x.2 y.2 h)

omit [Finite X] in
theorem range_barHom {P : Subgroup X} (hPM : P ≤ M) : (barHom hPM).range = barOf M P := by
  rw [barHom, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

@[expose] def barEquiv {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) : ↥P ≃* ↥(barOf M P) :=
  (MonoidHom.ofInjective (barHom_injective hPM hP)).trans
    (MulEquiv.subgroupCongr (range_barHom hPM))

theorem card_barOf {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) :
    Nat.card (barOf M P) = Nat.card P :=
  (Nat.card_congr (barEquiv hPM hP).toEquiv).symm

omit [Finite X] in
theorem barOf_inf_preimageOf {P : Subgroup X} (A : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) :
    barOf M (P ⊓ preimageOf M A) = barOf M P ⊓ A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, (mem_inf.mp hx).1, rfl⟩, (mem_preimageOf x.2).mp (mem_inf.mp hx).2⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hA⟩
    exact ⟨x, mem_inf.mpr ⟨hx, (mem_preimageOf x.2).mpr hA⟩, rfl⟩

theorem barOf_inf_centralizer {P : Subgroup X} (hPM : P ≤ M) (hP : IsPGroup 2 P) {y : X}
    (hyP : y ∈ P) :
    barOf M (P ⊓ centralizer {y}) =
      barOf M P ⊓ centralizer {(QuotientGroup.mk ⟨y, hPM hyP⟩ : ↥M ⧸ pPrimeCore 2 ↥M)} := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, (mem_inf.mp hx).1, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : (x : X) * y = y * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    change (QuotientGroup.mk (x * ⟨y, hPM hyP⟩) : ↥M ⧸ pPrimeCore 2 ↥M) =
      QuotientGroup.mk (⟨y, hPM hyP⟩ * x)
    rw [show x * ⟨y, hPM hyP⟩ = ⟨y, hPM hyP⟩ * x from Subtype.ext h1]
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    have h1 := mem_centralizer_singleton_iff.mp hc
    change (QuotientGroup.mk (x * ⟨y, hPM hyP⟩) : ↥M ⧸ pPrimeCore 2 ↥M) =
      QuotientGroup.mk (⟨y, hPM hyP⟩ * x) at h1
    have hxy : (x : X) * y ∈ P := mul_mem hx hyP
    have hyx : y * (x : X) ∈ P := mul_mem hyP hx
    exact mk_injOn hPM hP hxy hyx h1

omit [Finite X] in
theorem map_subtype_centralizer_mk {y : X} (hyM : y ∈ M) :
    (centralizer {(⟨y, hyM⟩ : ↥M)}).map M.subtype = centralizer ({y} : Set X) ⊓ M := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp hg')), g'.2⟩
  · rintro ⟨hgy, hgM⟩
    exact ⟨⟨g, hgM⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp hgy)), rfl⟩

theorem isSylowOf_barOf_centralizer {P : Subgroup X} {y : X} (hyM : y ∈ M) (hy2 : y ^ 2 = 1)
    (hP : IsSylowOf 2 P (centralizer ({y} : Set X) ⊓ M)) :
    IsSylowOf 2 (barOf M P)
      (centralizer {(QuotientGroup.mk ⟨y, hyM⟩ : ↥M ⧸ pPrimeCore 2 ↥M)}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyy : (⟨y, hyM⟩ : ↥M) * ⟨y, hyM⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hy2, Subgroup.coe_one])
  have hPM : P ≤ M := hP.le.trans inf_le_right
  have h1 : IsSylowOf 2 (P.subgroupOf M) (centralizer {(⟨y, hyM⟩ : ↥M)}) := by
    rw [← isSylowOf_map_subtype_iff M, map_subtype_centralizer_mk hyM, subgroupOf_map_subtype,
      inf_of_le_left hPM]
    exact hP
  have h2 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) h1
  rwa [← GSThmB.OddQuot.centralizer_singleton_map_eq hyy] at h2

theorem isSylowOf_barOf {P : Subgroup X} (hP : IsSylowOf 2 P M) :
    IsSylowOf 2 (barOf M P) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPM : P ≤ M := hP.le
  have h1 : IsSylowOf 2 (P.subgroupOf M) ⊤ := by
    rw [← isSylowOf_map_subtype_iff M, subgroupOf_map_subtype, inf_of_le_left hPM,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hP
  have h2 := HarrisLit.isSylowOf_map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) h1
  rwa [← MonoidHom.range_eq_map, QuotientGroup.range_mk'] at h2

end HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem Setting46e.exists_W (hs : Setting46e t L p f S w z V i j) :
    ∃ W : Subgroup X, IsSylowOf 2 W (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ∧
      V ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_isSylowOf_ge (hs.sylow_V.isPGroup.to_le inf_le_left) inf_le_right

end CFSG.ComponentClassification.HarrisLit
