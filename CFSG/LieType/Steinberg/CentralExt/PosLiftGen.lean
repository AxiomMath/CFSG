module

public import CFSG.LieType.Steinberg.CentralExt.PosLiftSplit

public section

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.PosLift

open CFSG.LieType.Steinberg

theorem commute_of_rev_sep {E G : Type*} [Group E] [Group G] {π : E →* G}
    (hcen : π.ker ≤ Subgroup.center E) {k : Type*} [Field k] {x y : k → G} {X Y : k → E}
    (hX : ∀ s t, X (s + t) = X s * X t) (hπX : ∀ s, π (X s) = x s) (hπY : ∀ s, π (Y s) = y s)
    (hxy : ∀ s t, x s * y t = y t * x s) {e : E} {a : k} (ha : a ≠ 1)
    (h1 : ∀ s, e * X s * e⁻¹ = X (a * s)) (h2 : ∀ t, e * Y t * e⁻¹ = Y t) (s t : k) :
    X s * Y t = Y t * X s := by
  have hc : ∀ s, ⁅X s, Y t⁆ ∈ Subgroup.center E := fun s => hcen (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hπX, hπY, commutatorElement_eq_one_iff_mul_comm]
    exact hxy s t)
  have hadd : ∀ s s', ⁅X (s + s'), Y t⁆ = ⁅X s, Y t⁆ * ⁅X s', Y t⁆ := fun s s' => by
    rw [hX]
    exact TorusLift.commutatorElement_mul_left_of_central (hc s')
  have hinv : ∀ s, ⁅X (a * s), Y t⁆ = ⁅X s, Y t⁆ := fun s => by
    have e1 : e * ⁅X s, Y t⁆ * e⁻¹ = ⁅X (a * s), Y t⁆ := by
      rw [conjugate_commutatorElement, h1, h2]
    rw [← e1, Subgroup.mem_center_iff.1 (hc s) e, mul_inv_cancel_right]
  have h0 : ∀ s, ⁅X ((a - 1) * s), Y t⁆ = 1 := fun s => by
    have h := hadd ((a - 1) * s) s
    rw [show (a - 1) * s + s = a * s by ring, hinv] at h
    exact right_eq_mul.1 h
  have h0s := h0 ((a - 1)⁻¹ * s)
  rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 ha), one_mul] at h0s
  exact commutatorElement_eq_one_iff_mul_comm.1 h0s

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
  {E : Type*} [Group E] {π : E →* K} {X : (Fin D.rank → ℤ) → k → E} {τ : Type*}
  {tor : τ → E} {χ : τ → (Fin D.rank → ℤ) → k}

theorem injOn_posUnipotent_lift' (hcen : π.ker ≤ Subgroup.center E) (hD : D.divisible = ∅)
    (hext : SteinbergExtras D n H)
    (hpar : ∀ γ ∈ posRoots D, ∀ g, g ∈ D.rootGroup γ ↔ ∃ c, x γ c = g)
    (hxadd : ∀ γ ∈ posRoots D, ∀ c d, x γ (c + d) = x γ c * x γ d)
    (hXadd : ∀ γ ∈ posRoots D, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ posRoots D, ∀ c, π (X γ c) = x γ c)
    (hXker : ∀ γ ∈ posRoots D, ∀ c, x γ c = 1 → X γ c = 1)
    (hT : ∀ j, ∀ γ ∈ posRoots D, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ a ∈ posRoots D, ∀ b ∈ posRoots D, a ≠ b → (∃ j, χ j a = 1 ∧ χ j b ≠ 1) ∨
      ∀ t c, X a t * X b c * (X a t)⁻¹ ∈ ⨆ (ε : Fin D.rank → ℤ)
        (_ : ε ∈ posRoots D ∧ (ε = b ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • a + p.2 • b)),
          chevRoot X ε) :
    Set.InjOn π ((⨆ γ ∈ posRoots D, chevRoot X γ : Subgroup E) : Set E) := by
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list (S := posRoots D)
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots.subset fun _ h => h.1) ht
  have hsub : (⨆ γ ∈ posRoots D, chevRoot X γ) = ⨆ v ∈ L, chevRoot X v := by
    simp only [← hmem]
  rw [hsub]
  have hL : ∀ v ∈ L, v ∈ posRoots D := fun v hv => (hmem v).1 hv
  refine HalfSpaceLift.injOn_list' hcen ht hnd hs (fun v hv => hXadd v (hL v hv))
    (fun v hv => hxadd v (hL v hv)) (fun v hv => hXker v (hL v hv))
    (fun v hv => hπX v (hL v hv)) ?_ ?_ (fun j v hv => hT j v (hL v hv)) ?_
  · intro a ha b hb hab y hy z hz
    obtain ⟨ha1, ha2⟩ := hL a ha
    obtain ⟨hb1, hb2⟩ := hL b hb
    rw [chevRoot_eq_rootGroup (hpar a (hL a ha)) (hxadd a (hL a ha))] at hy
    rw [chevRoot_eq_rootGroup (hpar b (hL b hb)) (hxadd b (hL b hb))] at hz
    have hli : LinIndepPair a b := by
      by_contra h
      rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD ha1 hb1 h with h | h
      · exact hab h.symm
      · rw [h] at hb2
        have : ht (-a) = -ht a := by simp [ht, Finset.sum_neg_distrib]
        rw [this] at hb2
        linarith
    have hc := hext.commutator_mem a ha1 b hb1 hli y hy z hz
    refine (show (⨆ ε ∈ openCone D.roots a b, D.rootGroup ε) ≤
      ⨆ c ∈ L, ⨆ (_ : min (ht a) (ht b) < ht c), chevRoot x c from
        iSup₂_le fun ε hε => ?_) hc
    obtain ⟨hεr, i, j, hi, hj, rfl⟩ := hε
    have hht : ht (i • a + j • b) = i * ht a + j * ht b := by
      simp [ht, Finset.sum_add_distrib, Finset.mul_sum]
    have hf : min (ht a) (ht b) < ht (i • a + j • b) := by
      rw [hht]
      have h1 : (1 : ℤ) ≤ i := by exact_mod_cast hi
      have h2 : (1 : ℤ) ≤ j := by exact_mod_cast hj
      have := min_le_left (ht a) (ht b)
      nlinarith
    have hpos : i • a + j • b ∈ posRoots D := ⟨hεr, (min_lt_iff.1 hf).elim
      (fun h => ha2.trans h) (fun h => hb2.trans h)⟩
    rw [← chevRoot_eq_rootGroup (hpar _ hpos) (hxadd _ hpos)]
    exact le_iSup₂_of_le (f := fun c (_ : c ∈ L) => ⨆ (_ : min (ht a) (ht b) < ht c),
      chevRoot x c) _ ((hmem _).2 hpos) (le_iSup_of_le hf le_rfl)
  · intro F F' hF hF' hFF' v hv
    refine hext.prodInjective_pos L hnd (fun γ => ?_) hs F F'
      (fun v hv => chevRoot_eq_rootGroup (hpar v (hL v hv)) (hxadd v (hL v hv)) ▸ hF v hv)
      (fun v hv => chevRoot_eq_rootGroup (hpar v (hL v hv)) (hxadd v (hL v hv)) ▸ hF' v hv)
      hFF' v hv
    rw [hmem γ]
    refine ⟨fun h => ⟨h.1, h.2, fun δ hδ e => ?_⟩, fun h => ⟨h.1, h.2.1⟩⟩
    exact two_smul_notMem_roots D.isFiniteType hD hδ (e ▸ h.1)
  · intro a ha b hb hab
    refine (hsep a (hL a ha) b (hL b hb) hab).imp id fun h t c => ?_
    refine (show (⨆ (ε : Fin D.rank → ℤ) (_ : ε ∈ posRoots D ∧ (ε = b ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧
        0 < p.2 ∧ ε = p.1 • a + p.2 • b)), chevRoot X ε) ≤
        ⨆ v ∈ L, ⨆ (_ : ht a < ht v ∨ v = b), chevRoot X v from
      iSup₂_le fun ε hε => ?_) (h t c)
    obtain ⟨hεp, rfl | ⟨p, hp1, hp2, rfl⟩⟩ := hε
    · exact le_iSup₂_of_le (f := fun v (_ : v ∈ L) => ⨆ (_ : ht a < ht v ∨ v = ε),
        chevRoot X v) ε hb (le_iSup_of_le (Or.inr rfl) le_rfl)
    · have ha2 := (hL a ha).2
      have hb2 := (hL b hb).2
      have hf : ht a < ht (p.1 • a + p.2 • b) := by
        have hht : ht (p.1 • a + p.2 • b) = p.1 * ht a + p.2 * ht b := by
          simp [ht, Finset.sum_add_distrib, Finset.mul_sum]
        rw [hht]
        have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
        have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
        nlinarith
      exact le_iSup₂_of_le (f := fun v (_ : v ∈ L) => ⨆ (_ : ht a < ht v ∨ v = b),
        chevRoot X v) _ ((hmem _).2 hεp) (le_iSup_of_le (Or.inl hf) le_rfl)

theorem exists_section_of_posLift' [Finite E] [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (hD : D.divisible = ∅) {p : ℕ}
    [hp : Fact p.Prime] (hXp : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hTp : p.Coprime (Nat.card (⨆ i, H i : Subgroup K)))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker)
    (hpar : ∀ γ ∈ posRoots D, ∀ g, g ∈ D.rootGroup γ ↔ ∃ c, x γ c = g)
    (hxadd : ∀ γ ∈ posRoots D, ∀ c d, x γ (c + d) = x γ c * x γ d)
    (hXadd : ∀ γ ∈ posRoots D, ∀ c d, X γ (c + d) = X γ c * X γ d)
    (hπX : ∀ γ ∈ posRoots D, ∀ c, π (X γ c) = x γ c)
    (hXker : ∀ γ ∈ posRoots D, ∀ c, x γ c = 1 → X γ c = 1)
    (hT : ∀ j, ∀ γ ∈ posRoots D, ∀ c, tor j * X γ c * (tor j)⁻¹ = X γ (χ j γ * c))
    (hsep : ∀ a ∈ posRoots D, ∀ b ∈ posRoots D, a ≠ b → (∃ j, χ j a = 1 ∧ χ j b ≠ 1) ∨
      ∀ t c, X a t * X b c * (X a t)⁻¹ ∈ ⨆ (ε : Fin D.rank → ℤ)
        (_ : ε ∈ posRoots D ∧ (ε = b ∨ ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ ε = p.1 • a + p.2 • b)),
          chevRoot X ε) :
    ∃ σ : K →* E, ∀ g, π (σ g) = g := by
  set Ũ : Subgroup E := ⨆ γ ∈ posRoots D, chevRoot X γ
  have hinj := injOn_posUnipotent_lift' hcen hD hext hpar hxadd hXadd hπX hXker hT hsep
  have hmap : Ũ.map π = posUnipotent D := by
    rw [Subgroup.map_iSup]
    refine iSup_congr fun γ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_congr fun hγ => ?_
    rw [chevRoot, MonoidHom.map_closure, ← Set.range_comp,
      show (⇑π ∘ X γ) = x γ from funext fun c => hπX γ hγ c, ← chevRoot,
      chevRoot_eq_rootGroup (hpar γ hγ) (hxadd γ hγ)]
  let φ : Ũ →* posUnipotent D :=
    { toFun := fun g => ⟨π g, by rw [← hmap]; exact Subgroup.mem_map_of_mem π g.2⟩
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h)), fun u => ?_⟩
    have hu : (u : K) ∈ Ũ.map π := by rw [hmap]; exact u.2
    obtain ⟨g, hg, hgu⟩ := hu
    exact ⟨⟨g, hg⟩, Subtype.ext hgu⟩
  let e := MulEquiv.ofBijective φ hφ
  let s : posUnipotent D →* E := Ũ.subtype.comp e.symm.toMonoidHom
  have hs : ∀ u : posUnipotent D, π (s u) = u := fun u => by
    have := congrArg Subtype.val (e.apply_symm_apply u)
    exact this
  exact CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_coprime_index p π hπ hcen hpk
    (posUnipotent D) (BorelIndex.coprime_index_posUnipotent hct hext hBU hXp hTp) s hs

end CFSG.LieType.Steinberg.CentralExt.PosLift
