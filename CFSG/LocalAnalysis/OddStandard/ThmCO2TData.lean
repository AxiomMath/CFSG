module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.LocalAnalysis.OddStandard.ThmCO2T

public section

namespace CFSG.OddStandard.ThmC.O2

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

section Embedding

variable {G : Type} [Group G] {F : Type} [Field F]

def emb (S : Subgroup G) (e : S ≃* UT3 F) : UT3 F →* G :=
  S.subtype.comp e.symm.toMonoidHom

theorem emb_injective (S : Subgroup G) (e : S ≃* UT3 F) : Function.Injective (emb S e) :=
  S.subtype_injective.comp e.symm.injective

theorem emb_mem_iff (S : Subgroup G) (e : S ≃* UT3 F) (g : G) :
    g ∈ S ↔ ∃ x, emb S e x = g := by
  constructor
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp [emb]⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

end Embedding

section Fields

open CFSG.OddStandard.ThmC.O2.TL

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] [Finite F] {S : Subgroup G}
  {ι : UT3 F →* G} (hι : Function.Injective ι) (hS : ∀ g : G, g ∈ S ↔ ∃ x, ι x = g)

include hι hS

omit [Finite F] in
omit [CharP F 2] in
theorem fld_mem_Z (g : G) : g ∈ (zT F).map ι ↔ g ∈ S ∧ ∀ s ∈ S, g * s = s * g := by
  constructor
  · intro hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
    refine ⟨(hS _).2 ⟨z, rfl⟩, fun s hs => ?_⟩
    obtain ⟨y, rfl⟩ := (hS s).1 hs
    rw [← map_mul, ← map_mul, (mem_zT_iff z).1 hz y]
  · rintro ⟨hg, hc⟩
    obtain ⟨x, rfl⟩ := (hS g).1 hg
    refine Subgroup.mem_map_of_mem ι ((mem_zT_iff x).2 fun y => hι ?_)
    rw [map_mul, map_mul]
    exact hc _ ((hS _).2 ⟨y, rfl⟩)

omit [Finite F] hι in
omit [CharP F 2] in
theorem fld_normal_dich (N : Subgroup G) (hNS : N ≤ S)
    (hN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) : N ≤ (zT F).map ι ∨ (zT F).map ι ≤ N := by
  have hnorm : (N.comap ι).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact hN _ ((hS _).2 ⟨g, rfl⟩) _ hn
  rcases normal_dich_T (N.comap ι) hnorm with h | h
  · left
    intro n hn
    obtain ⟨x, rfl⟩ := (hS n).1 (hNS hn)
    exact Subgroup.mem_map_of_mem ι (h (Subgroup.mem_comap.2 hn))
  · right
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_comap.1 (h hx)

omit [Finite F] in
theorem fld_elemAb_le (E : Subgroup G) (hES : E ≤ S) (hsq : ∀ x ∈ E, x * x = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : E ≤ (aT F).map ι ∨ E ≤ (bT F).map ι := by
  have h1 : ∀ x ∈ E.comap ι, x * x = 1 := fun x hx =>
    hι (by rw [map_mul, map_one]; exact hsq _ (Subgroup.mem_comap.1 hx))
  have h2 : ∀ x ∈ E.comap ι, ∀ y ∈ E.comap ι, x * y = y * x := fun x hx y hy =>
    hι (by
      rw [map_mul, map_mul]
      exact hc _ (Subgroup.mem_comap.1 hx) _ (Subgroup.mem_comap.1 hy))
  rcases elemAb_le_T (E.comap ι) h1 h2 with h | h
  · left
    intro g hg
    obtain ⟨x, rfl⟩ := (hS g).1 (hES hg)
    exact Subgroup.mem_map_of_mem ι (h (Subgroup.mem_comap.2 hg))
  · right
    intro g hg
    obtain ⟨x, rfl⟩ := (hS g).1 (hES hg)
    exact Subgroup.mem_map_of_mem ι (h (Subgroup.mem_comap.2 hg))

theorem fld_extremal (hF : Nat.card F = 4) (z : G) (hz : z ∈ (zT F).map ι) (hz1 : z ≠ 1)
    (a : G) (haS : a ∈ S) (haZ : a ∉ (zT F).map ι) :
    ∃ s ∈ S, ∃ t ∈ S, s * a * s⁻¹ * a⁻¹ ∈ zpowers z ∧ t * a * t⁻¹ * a⁻¹ ∈ zpowers z ∧
      s * t * s⁻¹ * t⁻¹ ∉ zpowers z := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨a', rfl⟩ := (hS a).1 haS
  have hz1' : z' ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have ha' : a' ∉ zT F := fun h => haZ (Subgroup.mem_map_of_mem ι h)
  obtain ⟨s, t, h1, h2, h3⟩ := extremal_T hF z' hz' hz1' a' ha'
  have hmz : ∀ w : UT3 F, ι w ∈ zpowers (ι z') ↔ w ∈ zpowers z' := fun w => by
    rw [← MonoidHom.map_zpowers]
    exact Subgroup.mem_map_iff_mem hι
  refine ⟨ι s, (hS _).2 ⟨s, rfl⟩, ι t, (hS _).2 ⟨t, rfl⟩, ?_, ?_, ?_⟩
  · have := (hmz _).2 h1
    simpa only [map_mul, map_inv] using this
  · have := (hmz _).2 h2
    simpa only [map_mul, map_inv] using this
  · intro h
    apply h3
    rw [← hmz]
    simpa only [map_mul, map_inv] using h

omit [CharP F 2] in
theorem fld_diag (hF : Nat.card F = 4) (g : G) (hg : g ∈ normalizer (S : Set G))
    (hz : ∀ z ∈ (zT F).map ι, g * z * g⁻¹ = z)
    (ha : ∀ a ∈ (aT F).map ι, g * a * g⁻¹ ∈ (aT F).map ι)
    (hb : ∀ b ∈ (bT F).map ι, g * b * g⁻¹ ∈ (bT F).map ι) :
    (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ (zT F).map ι) ∨
      ((∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ (zT F).map ι → s ∈ (zT F).map ι) ∧
        ∀ s ∈ S, g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ ∈ (zT F).map ι) := by
  have hmem : ∀ x : UT3 F, ι x ∈ S := fun x => (hS _).2 ⟨x, rfl⟩
  have hgS : ∀ x : UT3 F, g * ι x * g⁻¹ ∈ S := fun x =>
    (mem_set_normalizer_iff.1 hg _).1 (hmem x)
  have hgS' : ∀ x : UT3 F, g⁻¹ * ι x * g ∈ S := fun x =>
    (mem_set_normalizer_iff''.1 hg _).1 (hmem x)
  have hex : ∀ x : UT3 F, ∃ y, ι y = g * ι x * g⁻¹ := fun x => (hS _).1 (hgS x)
  have hex' : ∀ x : UT3 F, ∃ y, ι y = g⁻¹ * ι x * g := fun x => (hS _).1 (hgS' x)
  choose φ₀ hφ₀ using hex
  choose ψ₀ hψ₀ using hex'
  let φ : MulAut (UT3 F) :=
    { toFun := φ₀
      invFun := ψ₀
      left_inv := fun x => hι (by simp only [hψ₀, hφ₀]; group)
      right_inv := fun x => hι (by simp only [hφ₀, hψ₀]; group)
      map_mul' := fun x y => hι (by simp only [hφ₀, map_mul]; group) }
  have key : ∀ x, ι (φ x) = g * ι x * g⁻¹ := hφ₀
  have hz' : ∀ z ∈ zT F, φ z = z := fun z hz' =>
    hι (by rw [key]; exact hz _ (Subgroup.mem_map_of_mem ι hz'))
  have ha' : ∀ a ∈ aT F, φ a ∈ aT F := fun a ha' => by
    have := ha _ (Subgroup.mem_map_of_mem ι ha')
    rw [← key] at this
    exact (Subgroup.mem_map_iff_mem hι).1 this
  have hb' : ∀ b ∈ bT F, φ b ∈ bT F := fun b hb' => by
    have := hb _ (Subgroup.mem_map_of_mem ι hb')
    rw [← key] at this
    exact (Subgroup.mem_map_iff_mem hι).1 this
  have hconj : ∀ s' : UT3 F, g * ι s' * g⁻¹ * (ι s')⁻¹ = ι (φ s' * s'⁻¹) := fun s' => by
    rw [map_mul, map_inv, key]
  rcases diag_T hF φ hz' ha' hb' with h | ⟨h1, h2⟩
  · left
    intro s hs
    obtain ⟨s', rfl⟩ := (hS s).1 hs
    rw [hconj]
    exact Subgroup.mem_map_of_mem ι (h s')
  · right
    refine ⟨fun s hs hsz => ?_, fun s hs => ?_⟩
    · obtain ⟨s', rfl⟩ := (hS s).1 hs
      rw [hconj] at hsz
      exact Subgroup.mem_map_of_mem ι (h1 s' ((Subgroup.mem_map_iff_mem hι).1 hsz))
    · obtain ⟨s', rfl⟩ := (hS s).1 hs
      have h3 : g ^ 3 * ι s' * (g ^ 3)⁻¹ * (ι s')⁻¹ = ι (φ (φ (φ s')) * s'⁻¹) := by
        have e3 : g ^ 3 = g * g * g := by rw [pow_succ, pow_succ, pow_one]
        rw [map_mul, map_inv, key, key, key, e3]
        group
      rw [h3]
      exact Subgroup.mem_map_of_mem ι (h2 s')

end Fields

section Main

open CFSG.OddStandard.ThmC.O2.TL

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] [Finite F]

theorem tData_of_iso (hF : Nat.card F = 4) (S : Subgroup G) (ι : UT3 F →* G)
    (hι : Function.Injective ι) (hS : ∀ g : G, g ∈ S ↔ ∃ x, ι x = g)
    (hcard : Nat.card S = 64) : Nonempty (TData S) := by
  refine ⟨{
    Z := (zT F).map ι
    A := (aT F).map ι
    B := (bT F).map ι
    Z_le_A := Subgroup.map_mono zT_le_aT
    Z_le_B := Subgroup.map_mono zT_le_bT
    A_le_S := by
      rintro _ ⟨x, -, rfl⟩
      exact (hS _).2 ⟨x, rfl⟩
    B_le_S := by
      rintro _ ⟨x, -, rfl⟩
      exact (hS _).2 ⟨x, rfl⟩
    card_S := hcard
    card_Z := (Subgroup.card_map_of_injective hι).trans (card_zT hF)
    card_A := (Subgroup.card_map_of_injective hι).trans (card_aT hF)
    card_B := (Subgroup.card_map_of_injective hι).trans (card_bT hF)
    A_ne_B := fun h => aT_ne_bT (Subgroup.map_injective hι h)
    mem_Z := fld_mem_Z hι hS
    Z_sq := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      rw [← map_mul, zT_sq x hx, map_one]
    comm_mem_Z := by
      intro x hx y hy
      obtain ⟨x', rfl⟩ := (hS x).1 hx
      obtain ⟨y', rfl⟩ := (hS y).1 hy
      have := Subgroup.mem_map_of_mem ι (comm_mem_zT x' y')
      simpa only [map_mul, map_inv] using this
    sq_mem_Z := by
      intro x hx
      obtain ⟨x', rfl⟩ := (hS x).1 hx
      have := Subgroup.mem_map_of_mem ι (sq_mem_zT x')
      simpa only [map_mul] using this
    A_abel := by
      intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_mul, ← map_mul, aT_abel x' y' hx' hy']
    B_abel := by
      intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
      rw [← map_mul, ← map_mul, bT_abel x' y' hx' hy']
    A_sq := by
      intro x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_mul, aT_sq x' hx', map_one]
    B_sq := by
      intro x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_mul, bT_sq x' hx', map_one]
    AB_le_Z := by
      intro x hxA hxB
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hxA
      exact Subgroup.mem_map_of_mem ι (aT_inf_bT x' hx' ((Subgroup.mem_map_iff_mem hι).1 hxB))
    A_norm := by
      intro s hs a ha
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      have := Subgroup.mem_map_of_mem ι (aT_norm s' a' ha')
      simpa only [map_mul, map_inv] using this
    B_norm := by
      intro s hs b hb
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have := Subgroup.mem_map_of_mem ι (bT_norm s' b' hb')
      simpa only [map_mul, map_inv] using this
    invol := by
      intro x hx hxx
      obtain ⟨x', rfl⟩ := (hS x).1 hx
      have h : x' * x' = 1 := hι (by rw [map_mul, map_one]; exact hxx)
      rcases invol_T x' h with h' | h'
      · exact Or.inl (Subgroup.mem_map_of_mem ι h')
      · exact Or.inr (Subgroup.mem_map_of_mem ι h')
    cent_A := by
      intro a ha haZ s hs hsa
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      have haz : a' ∉ zT F := fun h => haZ (Subgroup.mem_map_of_mem ι h)
      have h : s' * a' = a' * s' := hι (by rw [map_mul, map_mul]; exact hsa)
      exact Subgroup.mem_map_of_mem ι (cent_aT a' ha' haz s' h)
    cent_B := by
      intro b hb hbZ s hs hsb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      have hbz : b' ∉ zT F := fun h => hbZ (Subgroup.mem_map_of_mem ι h)
      have h : s' * b' = b' * s' := hι (by rw [map_mul, map_mul]; exact hsb)
      exact Subgroup.mem_map_of_mem ι (cent_bT b' hb' hbz s' h)
    cent_not_A := by
      intro s hs hsA a ha has
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      have hs' : s' ∉ aT F := fun h => hsA (Subgroup.mem_map_of_mem ι h)
      have h : a' * s' = s' * a' := hι (by rw [map_mul, map_mul]; exact has)
      exact Subgroup.mem_map_of_mem ι (cent_not_aT s' hs' a' ha' h)
    cent_not_B := by
      intro s hs hsB b hb hbs
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      obtain ⟨s', rfl⟩ := (hS s).1 hs
      have hs' : s' ∉ bT F := fun h => hsB (Subgroup.mem_map_of_mem ι h)
      have h : b' * s' = s' * b' := hι (by rw [map_mul, map_mul]; exact hbs)
      exact Subgroup.mem_map_of_mem ι (cent_not_bT s' hs' b' hb' h)
    normal_dich := fld_normal_dich hS
    elemAb_le := fld_elemAb_le hι hS
    extremal := fun z hz hz1 a haS haZ => fld_extremal hι hS hF z hz hz1 a haS haZ
    diag := fun g hg hz ha hb => fld_diag hι hS hF g hg hz ha hb }⟩

end Main

theorem card_F4 : Nat.card F4 = 4 := by
  simpa using GaloisField.card 2 2 (by norm_num)

theorem tData_of_equiv {G : Type} [Group G] (S : Subgroup G)
    (e : S ≃* CFSG.GH74.GLS.Bg.TwoGroups.SylSL3_4) : Nonempty (TData S) := by
  have hcard : Nat.card S = 64 := (Nat.card_congr e.toEquiv).trans (TL.card_UT3 card_F4)
  exact tData_of_iso card_F4 S (emb S e) (emb_injective S e) (emb_mem_iff S e) hcard

end CFSG.OddStandard.ThmC.O2
