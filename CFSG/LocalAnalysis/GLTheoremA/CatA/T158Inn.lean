module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K156Norm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Facts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Group Ω] [Finite Ω]

theorem mem_zpowers_map_of_mem {A B : Type} [Group A] [Group B] (f : A →* B) {x z : A}
    (hz : z ∈ Subgroup.zpowers x) : f z ∈ Subgroup.zpowers (f x) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact Subgroup.mem_zpowers_iff.2 ⟨k, (map_zpow f x k).symm⟩

theorem mem_zpowers_sub {H : Subgroup G} {x : G} (hxH : x ∈ H) {a : G} (ha : a ∈ Subgroup.zpowers x) :
    ∃ haH : a ∈ H, (⟨a, haH⟩ : ↥H) ∈ Subgroup.zpowers (⟨x, hxH⟩ : ↥H) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine ⟨H.zpow_mem hxH k, Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩⟩
  simp

theorem mem_normalizer_subgroupOf' {H L : Subgroup G} {g : G} (hgH : g ∈ H)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    (⟨g, hgH⟩ : ↥H) ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 hg (y : G)

theorem subgroupOf_inf_centralizer {H X : Subgroup G} {x : G} (hXH : X ≤ H) (hxH : x ∈ H) :
    (X ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf H =
      X.subgroupOf H ⊓ Subgroup.centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H) := by
  apply Subgroup.map_injective (f := H.subtype) Subtype.coe_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hXH), map_centralizer_subgroupOf hXH hxH]

theorem glaPComponent_forth {p : ℕ} (hp : p.Prime) {H K L : Subgroup G} (hKH : K ≤ H) {x : G} (hxH : x ∈ H)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxp : x ^ p = 1) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) (hL : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) L) :
    GLAPComponent p ((K.subgroupOf H).map π ⊓ Subgroup.centralizer ({π ⟨x, hxH⟩} : Set Ω))
      ((L.subgroupOf H).map π) := by
  have hXH : K ⊓ Subgroup.centralizer ({x} : Set G) ≤ H := inf_le_left.trans hKH
  have h1 : GLAPComponent p ((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf H) (L.subgroupOf H) :=
    CFSG.LocalAnalysis.GLTheoremA.I2015.glaPComponent_subgroupOf hXH hL
  rw [subgroupOf_inf_centralizer hKH hxH, ← centralizer_zpowers_eq] at h1
  have hxp' : (⟨x, hxH⟩ : ↥H) ^ p = 1 := Subtype.ext hxp
  have hE : IsPGroup p (Subgroup.zpowers (⟨x, hxH⟩ : ↥H)) := isPGroup_zpowers_of_pow_eq_one hxp'
  have hEM : Subgroup.zpowers (⟨x, hxH⟩ : ↥H) ≤ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    Subgroup.zpowers_le.2 (mem_normalizer_subgroupOf' hxH hxK)
  have h2 := glaPComponent_map_inf_centralizer hp π hN hE hEM h1
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq] at h2
  exact h2

theorem innDiagOn_back {p : ℕ} (hp : p.Prime) {H : Subgroup G} {Y : Subgroup ↥H} {X : Subgroup G}
    (h : Y.map H.subtype = X) {π : ↥H →* Ω} (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H)
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) (hY : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.normalizer (Y : Set ↥H))
    (h' : InnDiagOn p (Subgroup.zpowers (π ⟨x, hxH⟩)) (Y.map π)) :
    InnDiagOn p (Subgroup.zpowers x) X := by
  refine innDiagOn_of_Omega (compIso hp h π hN) (Subgroup.zpowers_le.2 hxX) ?_ h'
  intro a ha
  obtain ⟨haH, hz⟩ := mem_zpowers_sub hxH ha
  exact ⟨π ⟨a, haH⟩, mem_zpowers_map_of_mem π hz,
    fun q q' => compIso_rel hp h π hN (Subgroup.zpowers_le.2 hY hz) q q'⟩

theorem nonInnDiag_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hn : NonInnDiag p x L) :
    NonInnDiag p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π) :=
  ⟨map_normalizer_mem π (mem_normalizer_subgroupOf' hxH hn.1),
    fun hin => hn.2 (innDiagOn_back hp (Subgroup.map_subgroupOf_eq_of_le hLH) hN hxH hn.1
      (mem_normalizer_subgroupOf' hxH hn.1) hin)⟩

theorem chev_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) (hc : IsChevSimple 2 (PSimple p L)) :
    IsChevSimple 2 (PSimple p ((L.subgroupOf H).map π)) :=
  isChevSimple_congr (psimpleIso (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN)) hc

theorem catalog_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs (PSimple p L) Q) :
    catalogIs (PSimple p ((L.subgroupOf H).map π)) Q :=
  (catalogIs_congr (psimpleIso (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN))).1 h

theorem innDiagOn_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (h : InnDiagOn p (Subgroup.zpowers x) L) :
    InnDiagOn p (Subgroup.zpowers (π ⟨x, hxH⟩)) ((L.subgroupOf H).map π) := by
  have hxn : x ∈ Subgroup.normalizer (L : Set G) := h.1 (Subgroup.mem_zpowers x)
  have hxY : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    mem_normalizer_subgroupOf' hxH hxn
  refine innDiagOn_to_Omega (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN)
    (Subgroup.zpowers_le.2 (map_normalizer_mem π hxY)) ?_ h
  intro a' ha'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
  refine ⟨x ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k, fun q q' => ?_⟩
  have hz : (⟨x, hxH⟩ : ↥H) ^ k ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    Subgroup.zpow_mem _ hxY k
  have := compIso_rel hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN hz q q'
  simpa [map_zpow] using this

theorem fieldOn_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hF : FieldOn p x L) : FieldOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π) := by
  have hxY := mem_normalizer_subgroupOf' hxH hxn
  exact fieldOn_to_Omega (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN)
    (map_normalizer_mem π hxY)
    (fun q q' => compIso_rel hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN hxY q q') hF

theorem fieldOn_back {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hF : FieldOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π)) : FieldOn p x L := by
  have hxY := mem_normalizer_subgroupOf' hxH hxn
  set e := compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN with he
  refine fieldOn_to_Omega e.symm hxn (fun q q' => ?_) hF
  have := compIso_rel hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN hxY (e.symm q) (e.symm q')
  rw [← he] at this
  simpa using this.symm

theorem nonInnDiag_back {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hn : NonInnDiag p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π)) : NonInnDiag p x L :=
  ⟨hxn, fun hin => hn.2 (innDiagOn_forth hp hLH hN hxH hin)⟩

theorem gfOn_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hg : GFOn p x L) : GFOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hxY := mem_normalizer_subgroupOf' hxH hxn
  have hcc : centCard2 p L x = centCard2 p ((L.subgroupOf H).map π) (π ⟨x, hxH⟩) :=
    centCard2_compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN (z := ⟨x, hxH⟩) hxY
  refine ⟨nonInnDiag_forth hp hLH hN hxH h1, ?_, ?_⟩
  · rintro ⟨hp3, hT⟩
    exact h2 ⟨hp3, (isTD4_congr hp3 (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN)).2 hT⟩
  · rw [← hcc, ← card2_compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN]
    exact h3

theorem gfOn_back {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hg : GFOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π)) : GFOn p x L := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hxY := mem_normalizer_subgroupOf' hxH hxn
  have hcc : centCard2 p L x = centCard2 p ((L.subgroupOf H).map π) (π ⟨x, hxH⟩) :=
    centCard2_compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN (z := ⟨x, hxH⟩) hxY
  refine ⟨nonInnDiag_back hp hLH hN hxH hxn h1, ?_, ?_⟩
  · rintro ⟨hp3, hT⟩
    exact h2 ⟨hp3, (isTD4_congr hp3 (compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN)).1 hT⟩
  · rw [hcc, card2_compIso hp (Subgroup.map_subgroupOf_eq_of_le hLH) π hN]
    exact h3

theorem fgOn_forth {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hg : FGOn p x L) : FGOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π) :=
  hg.elim (fun h => Or.inl (fieldOn_forth hp hLH hN hxH hxn h))
    (fun h => Or.inr (gfOn_forth hp hLH hN hxH hxn h))

theorem fgOn_back {p : ℕ} (hp : p.Prime) {H L : Subgroup G} (hLH : L ≤ H) {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x : G} (hxH : x ∈ H) (hxn : x ∈ Subgroup.normalizer (L : Set G))
    (hg : FGOn p (π ⟨x, hxH⟩) ((L.subgroupOf H).map π)) : FGOn p x L :=
  hg.elim (fun h => Or.inl (fieldOn_back hp hLH hN hxH hxn h))
    (fun h => Or.inr (gfOn_back hp hLH hN hxH hxn h))

private theorem eq_one_of_pow_prime_of_mem_ker {p : ℕ} (hp : p.Prime) {H : Type} [Group H] {π : H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {u : H} (hu : u ^ p = 1) (hπ : π u = 1) : u = 1 := by
  have hker : u ∈ π.ker := hπ
  by_contra hne
  have hord : orderOf u = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hu) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  exact hN (by rw [← hord]; exact Subgroup.orderOf_dvd_natCard π.ker hker)

theorem not_mem_zpowers_forth {p : ℕ} (hp : p.Prime) {H : Subgroup G} {π : ↥H →* Ω}
    (hN : ¬ p ∣ Nat.card π.ker) {x y : G} (hxH : x ∈ H) (hyH : y ∈ H) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (h : x ∉ Subgroup.zpowers y) :
    π ⟨x, hxH⟩ ∉ Subgroup.zpowers (π ⟨y, hyH⟩) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hcomm : Commute (⟨x, hxH⟩ : ↥H) (⟨y, hyH⟩ : ↥H) := Subtype.ext hxy
  have hx'p : (⟨x, hxH⟩ : ↥H) ^ p = 1 := Subtype.ext hxp
  have hy'p : (⟨y, hyH⟩ : ↥H) ^ p = 1 := Subtype.ext hyp
  have hu : ((⟨x, hxH⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H) ^ k) ^ p = 1 := by
    have hc : Commute (⟨x, hxH⟩ : ↥H)⁻¹ ((⟨y, hyH⟩ : ↥H) ^ k) := (hcomm.zpow_right k).inv_left
    rw [hc.mul_pow, inv_pow, hx'p, inv_one, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hy'p, one_zpow]
  have hπu : π ((⟨x, hxH⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H) ^ k) = 1 := by
    simp [map_mul, map_inv, map_zpow, hk]
  have h1 : (⟨x, hxH⟩ : ↥H)⁻¹ * (⟨y, hyH⟩ : ↥H) ^ k = 1 := eq_one_of_pow_prime_of_mem_ker hp hN hu hπu
  apply h
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have h2 : (⟨x, hxH⟩ : ↥H) = (⟨y, hyH⟩ : ↥H) ^ k := inv_mul_eq_one.1 h1
  have h3 := congrArg Subtype.val h2
  simpa using h3.symm

end Transport

theorem i158Inn_of_fact {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : T158InnFactOmega p) {X K B : Subgroup G} {x₁ x₂ : G} {L₁ L₂ : Subgroup G}
    (h : I158Base p X K B x₁ x₂ L₁ L₂) (hf12 : FieldOn p x₁ L₂) (hf21 : FieldOn p x₂ L₁)
    (hu1 : catalogIs (PSimple p L₁) S9.isU3eight) (hu2 : catalogIs (PSimple p L₂) S9.isU3eight) :
    InnDiagOn p (Subgroup.zpowers x₁) K ∧ InnDiagOn p (Subgroup.zpowers x₂) K := by
  obtain ⟨hKG, hK, hBel, hBX, -, hx1B, hx2B, -, -, hL1, -, hL2, -⟩ := h
  have hx1X : x₁ ∈ X := hBX hx1B
  have hx2X : x₂ ∈ X := hBX hx2B
  have hN1 : x₁ ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component hp hK hx1X
      (inf_le_left.trans hK.1) inf_le_left hL2 hf12.1
  have hN2 : x₂ ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component hp hK hx2X
      (inf_le_left.trans hK.1) inf_le_left hL1 hf21.1
  have hCatK : CFSG.Open.IsCatalogGroup (PSimple p K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient'
      ((hKG.of_le hK.1).quotient _) (isQuasisimple_pQuot_of_glaPComponent hp hK)
  set H : Subgroup G := K ⊔ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hHdef
  have hK1 : K ≤ K ⊔ Subgroup.zpowers x₁ := le_sup_left
  have hZ1 : Subgroup.zpowers x₁ ≤ K ⊔ Subgroup.zpowers x₁ := le_sup_right
  have hK1H : K ⊔ Subgroup.zpowers x₁ ≤ H := le_sup_left
  have hZ2H : Subgroup.zpowers x₂ ≤ H := le_sup_right
  have hKH : K ≤ H := hK1.trans hK1H
  have hx1H : x₁ ∈ H := hK1H (hZ1 (Subgroup.mem_zpowers x₁))
  have hx2H : x₂ ∈ H := hZ2H (Subgroup.mem_zpowers x₂)
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hN1)) (Subgroup.zpowers_le.2 hN2)
  set M : Subgroup ↥H := K.subgroupOf H with hMdef
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hHnorm : ∀ g : ↥H, g ∈ Subgroup.normalizer (M : Set ↥H) := by
    intro g
    rw [Subgroup.normalizer_eq_top_iff.2 hMn]
    exact Subgroup.mem_top g
  have hN0n : (GLAPPrimeCoreOf p M).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
    rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
  have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
  set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
    have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hCatS : CFSG.Open.IsCatalogGroup (PSimple p S) := by
    obtain ⟨i, ⟨f⟩⟩ := hCatK
    exact ⟨i, ⟨(psimpleIso eK).symm.trans f⟩⟩
  set x1H : ↥H := ⟨x₁, hx1H⟩ with hx1Hdef
  set x2H : ↥H := ⟨x₂, hx2H⟩ with hx2Hdef
  have hx1p : x1H ^ p = 1 := Subtype.ext (hBel.2 x₁ hx1B)
  have hx2p : x2H ^ p = 1 := Subtype.ext (hBel.2 x₂ hx2B)
  have hcomm : x1H * x2H = x2H * x1H := by
    apply Subtype.ext
    have hB : (⟨x₁, hx1B⟩ : ↥B) * ⟨x₂, hx2B⟩ = ⟨x₂, hx2B⟩ * ⟨x₁, hx1B⟩ :=
      hBel.1.is_comm.comm _ _
    have hG : x₁ * x₂ = x₂ * x₁ := congrArg Subtype.val hB
    exact hG
  have hy1p : (π x1H) ^ p = 1 := by rw [← map_pow, hx1p, map_one]
  have hy2p : (π x2H) ^ p = 1 := by rw [← map_pow, hx2p, map_one]
  have hcommY : π x1H * π x2H = π x2H * π x1H := by rw [← map_mul, ← map_mul, hcomm]
  have hL1H : L₁ ≤ H := hL1.1.trans (inf_le_left.trans hKH)
  have hL2H : L₂ ≤ H := hL2.1.trans (inf_le_left.trans hKH)
  have hL1Ω := glaPComponent_forth hp hKH hx1H hN1 (hBel.2 x₁ hx1B) hN hL1
  have hL2Ω := glaPComponent_forth hp hKH hx2H hN2 (hBel.2 x₂ hx2B) hN hL2
  have hu1Ω := catalog_forth hp hL1H hN hu1
  have hu2Ω := catalog_forth hp hL2H hN hu2
  have hf12Ω := fieldOn_forth hp hL2H hN hx1H hf12.1 hf12
  have hf21Ω := fieldOn_forth hp hL1H hN hx2H hf21.1 hf21
  obtain ⟨o1, o2⟩ := hΩ.inn hp hp2 (↥H ⧸ N0) S (π x1H) (π x2H) ((L₁.subgroupOf H).map π)
    ((L₂.subgroupOf H).map π) hSn hqS hSp hCatS hy1p hy2p hcommY hL1Ω hu1Ω hL2Ω hu2Ω hf12Ω hf21Ω
  exact ⟨innDiagOn_back hp hMK hN hx1H hN1 (hHnorm x1H) o1,
    innDiagOn_back hp hMK hN hx2H hN2 (hHnorm x2H) o2⟩

theorem i158Inn_of_facts {G : Type} [Group G] [Finite G] (hΩ : ∀ p : ℕ, T158InnFactOmega p) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G) (x₁ x₂ : G) (L₁ L₂ : Subgroup G),
      I158Base p X K B x₁ x₂ L₁ L₂ → FieldOn p x₁ L₂ → FieldOn p x₂ L₁ →
      catalogIs (PSimple p L₁) S9.isU3eight → catalogIs (PSimple p L₂) S9.isU3eight →
      InnDiagOn p (Subgroup.zpowers x₁) K ∧ InnDiagOn p (Subgroup.zpowers x₂) K :=
  fun p hp hp2 _ _ _ _ _ _ _ h hf12 hf21 hu1 hu2 => i158Inn_of_fact hp hp2 (hΩ p) h hf12 hf21 hu1 hu2

theorem i158FG_of_fact {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : T158InnFactOmega p) {X K : Subgroup G} {x y : G} {J : Subgroup G}
    (hK : GLAPComponent p X K) (hc : IsChevSimple 2 (PSimple p K)) (hxp : x ^ p = 1) (hyp : y ^ p = 1)
    (hxy : x * y = y * x) (hxny : x ∉ Subgroup.zpowers y) (hynx : y ∉ Subgroup.zpowers x)
    (hInn : InnDiagOn p (Subgroup.zpowers x) K) (hF : FieldOn p y K)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set G)) : FGOn p y J := by
  have hN1 : x ∈ Subgroup.normalizer (K : Set G) := hInn.1 (Subgroup.mem_zpowers x)
  have hN2 : y ∈ Subgroup.normalizer (K : Set G) := hF.1
  set H : Subgroup G := K ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y with hHdef
  have hK1H : K ⊔ Subgroup.zpowers x ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_left.trans hK1H
  have hxH : x ∈ H := hK1H (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hN1)) (Subgroup.zpowers_le.2 hN2)
  set M : Subgroup ↥H := K.subgroupOf H with hMdef
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hN0n : (GLAPPrimeCoreOf p M).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
    rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
  have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
  set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
    have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hcS : IsChevSimple 2 (PSimple p S) := isChevSimple_congr (psimpleIso eK) hc
  have hxp' : (⟨x, hxH⟩ : ↥H) ^ p = 1 := Subtype.ext hxp
  have hyp' : (⟨y, hyH⟩ : ↥H) ^ p = 1 := Subtype.ext hyp
  have hxpΩ : (π ⟨x, hxH⟩) ^ p = 1 := by rw [← map_pow, hxp', map_one]
  have hypΩ : (π ⟨y, hyH⟩) ^ p = 1 := by rw [← map_pow, hyp', map_one]
  have hcommΩ : π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hxy)
  have hJH : J ≤ H := hJ.1.trans (inf_le_left.trans hKH)
  have hxnyΩ := not_mem_zpowers_forth hp hN hxH hyH hxp hyp hxy hxny
  have hynxΩ := not_mem_zpowers_forth hp hN hyH hxH hyp hxp hxy.symm hynx
  have hInnΩ := innDiagOn_forth hp hKH hN hxH hInn
  have hFΩ := fieldOn_forth hp hKH hN hyH hN2 hF
  have hJΩ := glaPComponent_forth hp hKH hxH hN1 hxp hN hJ
  have hJyΩ : π ⟨y, hyH⟩ ∈ Subgroup.normalizer (((J.subgroupOf H).map π : Subgroup _) : Set _) :=
    map_normalizer_mem π (mem_normalizer_subgroupOf' hyH hJy)
  exact fgOn_back hp hJH hN hyH hJy
    (hΩ.fg hp hp2 (↥H ⧸ N0) S (π ⟨x, hxH⟩) (π ⟨y, hyH⟩) ((J.subgroupOf H).map π) hSn hqS hSp hcS hxpΩ
      hypΩ hcommΩ hxnyΩ hynxΩ hInnΩ hFΩ hJΩ hJyΩ)

theorem i158FG_of_facts {G : Type} [Group G] [Finite G] (hΩ : ∀ p : ℕ, T158InnFactOmega p) : I158FGUp G :=
  fun p hp hp2 _ _ _ _ _ hK hc hxp hyp hxy hxny hynx hInn hF hJ hJy =>
    i158FG_of_fact hp hp2 (hΩ p) hK hc hxp hyp hxy hxny hynx hInn hF hJ hJy

end CFSG.LocalAnalysis.GLTheoremA.T158

end
