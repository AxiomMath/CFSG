module

public import CFSG.GH74.GLS.Stage4.T2F1LocFin

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

structure GChart {G : Type} [Group G] {A B : Type} [Field A] [Field B] (f z : G)
    (ψ₁ : SL2 A →* G) (ψ₂ : SL2 B →* G) (g₁ : GL (Fin 2) A) (g₂ : GL (Fin 2) B) (t : G) : Prop where
  chart : ChartData ψ₁ ψ₂ g₁ g₂ z t
  cen₁ : ∀ M : SL2 A, ψ₁ M * f = f * ψ₁ M
  cen₂ : ∀ N : SL2 B, ψ₂ N * f = f * ψ₂ N
  tf : t * f = f * t
  zf : z * f = f * z
  two : ∀ y : G, y * f = f * y → y * z = z * y → (∃ k : ℕ, y ^ (2 ^ k) = 1) →
    y ∈ ChartData.Y₀ ψ₁ ψ₂ t

section Glue

theorem hyp94Loc_of_gchart
    {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {f z u t : G} {m : ℕ} (hm : 1 ≤ m)
    {A B : Type} [Field A] [Field B] [Finite A] [Finite B] (hA : Nat.card A = 3 ^ m)
    (hB : Nat.card B = 3 ^ m) {ψ₁ : SL2 A →* G} {ψ₂ : SL2 B →* G} {g₁ : GL (Fin 2) A}
    {g₂ : GL (Fin 2) B} (D : GChart f z ψ₁ ψ₂ g₁ g₂ t)
    (S : Sylow 2 G) (hSf : ∀ s ∈ (S : Subgroup G), s * f = f * s) (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s ∈ (S : Subgroup G), z * s = s * z)
    (hZS : ∀ x ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), x * s = s * x) → x ∈ Subgroup.zpowers z)
    (hu : u ∈ (S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hne : u ≠ z) (hzu : z * u = u * z)
    (hSiso : ∃ S' : Sylow 2 Gs, Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs)))
    (hlie : ∃ p fe : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel Gs .G2 0 p fe)
    (hfuse : ∃ a : G, f * a = a * f ∧ a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u) :
    ∃ hzC : z ∈ Subgroup.centralizer ({f} : Set G),
      CFSG.GH74.GLS.IVK.Hyp94Loc (↥(Subgroup.centralizer ({f} : Set G)) ⧸
        pPrimeCore 2 ↥(Subgroup.centralizer ({f} : Set G))) Gs
        (QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({f} : Set G)))) .G2 3 m := by
  set C : Subgroup G := Subgroup.centralizer ({f} : Set G) with hCdef
  have hmem : ∀ g : G, g ∈ C ↔ g * f = f * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hzC : z ∈ C := (hmem z).2 D.zf
  refine ⟨hzC, ?_⟩
  let ψ₁' : SL2 A →* ↥C := ψ₁.codRestrict C (fun M => (hmem _).2 (D.cen₁ M))
  let ψ₂' : SL2 B →* ↥C := ψ₂.codRestrict C (fun M => (hmem _).2 (D.cen₂ M))
  let z' : ↥C := ⟨z, hzC⟩
  let t' : ↥C := ⟨t, (hmem t).2 D.tf⟩
  have hD := D.chart
  have hD' : ChartData ψ₁' ψ₂' g₁ g₂ z' t' :=
    { inj₁ := fun M N h => hD.inj₁ (congrArg Subtype.val h)
      inj₂ := fun M N h => hD.inj₂ (congrArg Subtype.val h)
      comm := fun M N => Subtype.ext (hD.comm M N)
      neg₁ := Subtype.ext hD.neg₁
      neg₂ := Subtype.ext hD.neg₂
      zz := Subtype.ext hD.zz
      z_ne := fun h => hD.z_ne (congrArg Subtype.val h)
      inter := fun M N h => by
        rcases hD.inter M N (congrArg Subtype.val h) with h1 | h1
        · left; exact Subtype.ext h1
        · right; exact Subtype.ext h1
      tt := Subtype.ext hD.tt
      act₁ := fun M => Subtype.ext (hD.act₁ M)
      act₂ := fun N => Subtype.ext (hD.act₂ N)
      ns₁ := hD.ns₁
      ns₂ := hD.ns₂ }
  have hmapY : (ChartData.Y₀ ψ₁' ψ₂' t').map C.subtype = ChartData.Y₀ ψ₁ ψ₂ t := by
    simp only [ChartData.Y₀, Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_zpowers]
    rfl
  have htwo : ∀ y : ↥C, y * z' = z' * y → (∃ k : ℕ, y ^ (2 ^ k) = 1) →
      y ∈ ChartData.Y₀ ψ₁' ψ₂' t' := by
    intro y hyz ⟨k, hk⟩
    have hyf : (y : G) * f = f * y := (hmem _).1 y.2
    have h1 : (y : G) ∈ ChartData.Y₀ ψ₁ ψ₂ t :=
      D.two y hyf (congrArg Subtype.val hyz) ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [← hmapY] at h1
    exact (Subgroup.mem_map_iff_mem C.subtype_injective).1 h1
  have hSC : (S : Subgroup G) ≤ C := fun s hs => (hmem s).2 (hSf s hs)
  let SX : Sylow 2 ↥C := S.subtype hSC
  have hSX : ∀ x : ↥C, x ∈ (SX : Subgroup ↥C) ↔ (x : G) ∈ (S : Subgroup G) := fun _ => Iff.rfl
  have huC : u ∈ C := (hmem u).2 (hSf u hu)
  obtain ⟨S', ⟨eS'⟩⟩ := hSiso
  obtain ⟨a, hfa, haz, hau⟩ := hfuse
  have haC : a ∈ C := (hmem a).2 hfa.symm
  refine hyp94Loc_of_charts hm hA hB hD' htwo SX ((hSX z').2 hzS)
    (fun s hs => Subtype.ext (hzc s ((hSX s).1 hs)))
    (fun x hx hc => by
      have hx' : (x : G) ∈ (S : Subgroup G) := (hSX x).1 hx
      obtain ⟨k, hk⟩ := hZS x hx' (fun s hs => by
        have := hc ⟨s, hSC hs⟩ ((hSX _).2 hs)
        exact congrArg Subtype.val this)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)
    (u := ⟨u, huC⟩) ((hSX _).2 hu) (Subtype.ext hu2) (fun h => hu1 (congrArg Subtype.val h))
    (fun h => hne (congrArg Subtype.val h)) (Subtype.ext hzu)
    ⟨S', ⟨(Subgroup.subgroupOfEquivOfLe hSC).trans eS'⟩⟩ hlie
    ⟨⟨a, haC⟩, Subtype.ext haz, Subtype.ext hau⟩

end Glue

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
