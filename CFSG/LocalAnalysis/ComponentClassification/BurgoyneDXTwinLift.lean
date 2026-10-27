module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.TBLit

variable {X : Type} [Group X]

theorem oddCentralizerCore_subgroupOf_le [Finite X] {X' : Subgroup X} (t : X') :
    (oddCentralizerCore (t : X)).subgroupOf X' ≤ oddCentralizerCore t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({(t : X)} : Set X) with hC
  set C' := centralizer ({t} : Set X') with hC'
  set O := (pPrimeCore 2 C).map C.subtype with hO
  have hmemC : ∀ c : C', ((c : X') : X) ∈ C := by
    intro c
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2)
  let ι : C' →* C := ((X'.subtype.comp C'.subtype).codRestrict C hmemC)
  have hι : Function.Injective ι := by
    intro a b h
    have h' : ((ι a : C) : X) = ((ι b : C) : X) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  set N := (pPrimeCore 2 C).comap ι with hN
  have hNn : N.Normal := (pPrimeCore_normal (p := 2) (G := C)).comap ι
  have hNcop : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card (pPrimeCore 2 C) := by
      have := Subgroup.card_dvd_of_le (map_comap_le ι (pPrimeCore 2 C))
      rwa [Subgroup.card_map_of_injective hι] at this
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hNle : N ≤ pPrimeCore 2 C' := le_sSup ⟨hNn, hNcop⟩
  intro x hx
  rw [mem_subgroupOf] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hxC' : x ∈ C' := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    have h := mem_centralizer_singleton_iff.mp z.2
    show (x : X) * (t : X) = (t : X) * (x : X)
    rw [← hzx]
    exact h
  refine ⟨⟨x, hxC'⟩, hNle ?_, rfl⟩
  change ι ⟨x, hxC'⟩ ∈ pPrimeCore 2 C
  have : ι ⟨x, hxC'⟩ = z := Subtype.ext hzx.symm
  rw [this]
  exact hz

theorem actsProperly_of_subgroupOf {X' : Subgroup X} (t : X') {E A : Subgroup X} (hE : E ≤ X')
    (hA : A ≤ X')
    (h : ActsProperly t (E.subgroupOf X') (A.subgroupOf X') ⊥) :
    ActsProperly (t : X) E A ⊥ := by
  obtain ⟨h1, h2, e, he, a, ha, hea⟩ := h
  have hcl : closure (insert (t : X) (E : Set X)) =
      (closure (insert t ((E.subgroupOf X') : Set X'))).map X'.subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, SetLike.mem_coe, Set.mem_image, Subgroup.coe_subtype,
      mem_subgroupOf]
    constructor
    · rintro (rfl | hx)
      · exact ⟨t, Or.inl rfl, rfl⟩
      · exact ⟨⟨x, hE hx⟩, Or.inr hx, rfl⟩
    · rintro ⟨y, rfl | hy, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr hy
  have hnorm : ∀ g' : X', g' ∈ normalizer ((A.subgroupOf X' : Subgroup X') : Set X') →
      (g' : X) ∈ normalizer (A : Set X) := by
    intro g' hg'
    rw [mem_normalizer_iff] at hg' ⊢
    intro a
    constructor
    · intro haA
      have := (hg' ⟨a, hA haA⟩).mp (mem_subgroupOf.mpr haA)
      exact mem_subgroupOf.mp this
    · intro hgA
      have hmem : (g' : X) * a * (g' : X)⁻¹ ∈ X' := hA hgA
      have haX : a ∈ X' := by
        have := mul_mem (mul_mem (inv_mem g'.2) hmem) g'.2
        simpa [mul_assoc] using this
      have := (hg' ⟨a, haX⟩).mpr (mem_subgroupOf.mpr hgA)
      exact mem_subgroupOf.mp this
  refine ⟨?_, ?_, (e : X), mem_subgroupOf.mp he, (a : X), mem_subgroupOf.mp ha, ?_⟩
  · rw [hcl]
    rintro _ ⟨g', hg', rfl⟩
    obtain ⟨hgA, hgB⟩ := mem_inf.mp (h1 hg')
    refine mem_inf.mpr ⟨hnorm g' hgA, ?_⟩
    have htop : normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
      normalizer_eq_top_iff.mpr inferInstance
    rw [htop]
    exact mem_top _
  · intro g hg hcom
    rw [hcl] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := h2 g' hg' fun a' ha' => by
      have := hcom (a' : X) (mem_subgroupOf.mp ha')
      rw [mem_bot] at this ⊢
      exact Subtype.ext (by simpa [commutatorElement_def] using this)
    exact mem_subgroupOf.mp this
  · intro hc
    apply hea
    rw [mem_bot] at hc ⊢
    exact Subtype.ext (by simpa [commutatorElement_def] using hc)

theorem isSubnormal_of_subgroupOf {X' N : Subgroup X} [N.Normal] (hNX' : N ≤ X') (u : X')
    {S : Subgroup X} (hSN : S ≤ N)
    (h : ((S.subgroupOf X').subgroupOf (centralizer ({u} : Set X'))).IsSubnormal) :
    (S.subgroupOf (centralizer ({(u : X)} : Set X))).IsSubnormal := by
  set C := centralizer ({(u : X)} : Set X) with hC
  set C' := centralizer ({u} : Set X') with hC'
  set D := N.subgroupOf C with hD
  have hDn : D.Normal := inferInstance
  have hmemX' : ∀ d : D, ((d : C) : X) ∈ X' := fun d => hNX' (mem_subgroupOf.mp d.2)
  have hmemC' : ∀ d : D, (⟨((d : C) : X), hmemX' d⟩ : X') ∈ C' := by
    intro d
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (d : C).2
  let ι : D →* C' :=
    { toFun := fun d => ⟨⟨((d : C) : X), hmemX' d⟩, hmemC' d⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcomap : ((S.subgroupOf X').subgroupOf C').comap ι = (S.subgroupOf C).subgroupOf D := by
    ext d
    simp only [mem_comap, mem_subgroupOf]
    rfl
  have h1 : ((S.subgroupOf C).subgroupOf D).IsSubnormal := hcomap ▸ h.comap ι
  have hle : S.subgroupOf C ≤ D := by
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hSN hx
  exact IsSubnormal.trans hle h1 hDn.isSubnormal

end CFSG.ComponentClassification.Burgoyne.DX
