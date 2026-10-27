module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.TransferX
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.AltLeaf
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.CoreAux

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_alt_eight_centralizing (V K Z S : Subgroup X)
    (hVK : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hZV : Z ≤ V) (hSK : S ≤ K)
    (hSodd : ¬ 2 ∣ (S.subgroupOf K).index) (hSZ : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ = z)
    {n : ℕ} (hn : 9 ≤ n) (Φ : ↥K →* alternatingGroup (Fin n)) (hΦ : Function.Surjective Φ)
    (hΦS : IsPGroup 2 ((S.subgroupOf K).map Φ))
    (hΦodd : ¬ 2 ∣ ((S.subgroupOf K).map Φ).index)
    (π : ↥⁅V, K⁆ →* Multiplicative (altHeart n))
    (hker : ∀ u : ↥⁅V, K⁆, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπ : ∀ (l : ↥K) (u u' : ↥⁅V, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Perm (Fin n)) x) : altHeart n)) :
    ∃ φ : alternatingGroup (Fin 8) →* alternatingGroup (Fin n), Function.Injective φ ∧
      ∃ D : Subgroup ↥K, (∀ d ∈ D, ∀ z ∈ Z, (d : X) * z * (d : X)⁻¹ = z) ∧
        ∀ a, ∃ d ∈ D, Φ d = φ a := by
  classical
  obtain ⟨φ, hφinj, hφfix⟩ := exists_alt_eight_fixing hn _ hΦS hΦodd
  refine ⟨φ, hφinj, ?_⟩
  have hUV : ⁅V, K⁆ ≤ V := commutator_le_of_invariant V K hVK
  set H : Subgroup ↥K := φ.range.comap Φ with hH
  have hHfix : ∀ (h : ↥K), h ∈ H → ∀ x : evenWeight n,
      (∀ s' ∈ (S.subgroupOf K).map Φ, (QuotientAddGroup.mk (evenWeightPerm (s' : Perm (Fin n)) x) :
        altHeart n) = QuotientAddGroup.mk x) → evenWeightPerm (Φ h : Perm (Fin n)) x = x := by
    intro h hh x hx
    obtain ⟨a, ha⟩ := hh
    rw [← ha]
    exact hφfix x hx a
  have key : ∀ d ∈ ⁅H, H⁆, ∀ z ∈ Z, (d : X) * z * (d : X)⁻¹ = z := by
    intro d hd z hz
    have hzV := hZV hz
    have hzU : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ ⁅V, K⁆ := by
      intro k hk
      have h1 : ⁅z, k⁆ ∈ ⁅V, K⁆ := Subgroup.commutator_mem_commutator hzV hk
      have h2 : k * z * k⁻¹ * z⁻¹ = (⁅z, k⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [h2]; exact Subgroup.inv_mem _ h1
    obtain ⟨m, hmU, hm, hmS⟩ := exists_fixed_mem_comm_eq V ⁅V, K⁆ K S hVc hV2 hUV
      (fun k hk u hu => conj_mem_commutator V K hVK k hk hu) hSK hSodd z hzV hzU
      (fun s hs => hSZ s hs z hz)
    have hmV : m ∈ V := hUV hmU
    let um : ↥⁅V, K⁆ := ⟨m, hmU⟩
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π um))
    have hxS : ∀ s' ∈ (S.subgroupOf K).map Φ,
        (QuotientAddGroup.mk (evenWeightPerm (s' : Perm (Fin n)) x) : altHeart n) =
          QuotientAddGroup.mk x := by
      rintro s' ⟨s, hs, rfl⟩
      have hs' : (s : X) ∈ S := hs
      have h1 := hπ s um um (by show m = (s : X) * m * (s : X)⁻¹; exact (hmS _ hs').symm) x hx.symm
      rw [← h1, hx]
    have hA : ∀ h : ↥K, h ∈ H → ∀ k ∈ K,
        k * ((h : X) * m * (h : X)⁻¹ * m⁻¹) * k⁻¹ = (h : X) * m * (h : X)⁻¹ * m⁻¹ := by
      intro h hh k hk
      let um' : ↥⁅V, K⁆ := ⟨(h : X) * m * (h : X)⁻¹, conj_mem_commutator V K hVK h h.2 hmU⟩
      have e1 := hπ h um um' rfl x hx.symm
      have e2 : evenWeightPerm (Φ h : Perm (Fin n)) x = x := hHfix h hh x hxS
      have e3 : π um' = π um := by
        apply Multiplicative.toAdd.injective
        rw [e1, e2, hx]
      have e4 : π (um' * um⁻¹) = 1 := by rw [map_mul, map_inv, e3, mul_inv_cancel]
      have e5 := hker _ e4 k hk
      simpa [um, um'] using e5
    have hVmem : ∀ h : ↥K, (h : X) * m * (h : X)⁻¹ * m⁻¹ ∈ V := fun h =>
      V.mul_mem (hVK h h.2 m hmV) (V.inv_mem hmV)
    letI : CommGroup ↥V := { (inferInstance : Group ↥V) with
      mul_comm := fun a b => Subtype.ext (hVc _ a.2 _ b.2) }
    let θ : ↥H →* ↥V :=
      { toFun := fun h => ⟨((h : ↥K) : X) * m * ((h : ↥K) : X)⁻¹ * m⁻¹, hVmem h⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun h1 h2 => by
          apply Subtype.ext
          have hc := hA (h2 : ↥K) h2.2 ((h1 : ↥K) : X) (h1 : ↥K).2
          have hw := hVc _ (hVmem (h1 : ↥K)) _ (hVmem (h2 : ↥K))
          show (((h1 * h2 : ↥H) : ↥K) : X) * m * (((h1 * h2 : ↥H) : ↥K) : X)⁻¹ * m⁻¹ =
            (((h1 : ↥K) : X) * m * ((h1 : ↥K) : X)⁻¹ * m⁻¹) *
              (((h2 : ↥K) : X) * m * ((h2 : ↥K) : X)⁻¹ * m⁻¹)
          have hid : (((h1 * h2 : ↥H) : ↥K) : X) * m * (((h1 * h2 : ↥H) : ↥K) : X)⁻¹ * m⁻¹ =
              (((h1 : ↥K) : X) * (((h2 : ↥K) : X) * m * ((h2 : ↥K) : X)⁻¹ * m⁻¹) *
                ((h1 : ↥K) : X)⁻¹) * (((h1 : ↥K) : X) * m * ((h1 : ↥K) : X)⁻¹ * m⁻¹) := by
            show (((h1 : ↥K) : X) * ((h2 : ↥K) : X)) * m * (((h1 : ↥K) : X) * ((h2 : ↥K) : X))⁻¹ *
              m⁻¹ = _
            group
          rw [hid, hc, ← hw] }
    have hker' : ⁅(⊤ : Subgroup ↥H), ⊤⁆ ≤ θ.ker := by
      rw [Subgroup.commutator_le]
      intro g1 _ g2 _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have hc : ⁅H, H⁆ = Subgroup.map H.subtype ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hc] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    have h1 : θ d' = 1 := hker' hd'
    have h2 := congrArg Subtype.val h1
    have h3 : ((d' : ↥K) : X) * m * ((d' : ↥K) : X)⁻¹ * m⁻¹ = 1 := h2
    have h4 := hm (d' : ↥K) (d' : ↥K).2
    rw [h3] at h4
    have h5 : (((H.subtype d') : ↥K) : X) * z * (((H.subtype d') : ↥K) : X)⁻¹ = z := by
      have := mul_inv_eq_one.mp h4
      simpa using this
    exact h5
  refine ⟨⁅H, H⁆, fun d hd z hz => key d hd z hz, fun a => ?_⟩
  have h1 : ⁅H, H⁆.map Φ = φ.range := by
    rw [Subgroup.map_commutator, hH, Subgroup.map_comap_eq_self_of_surjective hΦ,
      MonoidHom.range_eq_map, ← Subgroup.map_commutator, alt_eight_perfect]
  have : φ a ∈ ⁅H, H⁆.map Φ := by rw [h1]; exact ⟨a, rfl⟩
  obtain ⟨d, hd, hda⟩ := this
  exact ⟨d, hd, hda⟩

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
