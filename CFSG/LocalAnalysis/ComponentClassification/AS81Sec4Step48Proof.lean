module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48Tim
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48NCert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step47
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Q47

section Coord

variable {G : Type} [Group G] {Q : Subgroup G} {z : G}

theorem exists_nstarCoord (hQC : Q ≤ centralizer ({z} : Set G)) (c : VCode Q z)
    (hs : VCode.Std Q z) {c₀ : Equiv.Perm (Fin 64)} (hc₀ : c₀ ∈ oV)
    (hN : ∀ n : ↥(normalizer (Q : Set G)), c₀⁻¹ * c.rho hs n * c₀ ∈ nstar) :
    ∃ (κ : ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z) → Fin 64)
      (δ : ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z) → Equiv.Perm (Fin 64)),
      NstarCoord ((Q.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (zpowers (zC z)))) κ δ := by
  classical
  set C := centralizer ({z} : Set G) with hC
  set π := QuotientGroup.mk' (zpowers (zC z)) with hπ
  set X := Q.subgroupOf C with hX
  have hzX : zpowers (zC z) ≤ X := zpowers_le.mpr (show (zC z : G) ∈ Q from hs.z_mem)
  have hker : π.ker = zpowers (zC z) := QuotientGroup.ker_mk' _
  have hXmem : ∀ x : ↥C, π x ∈ X.map π ↔ (x : G) ∈ Q := by
    intro x
    constructor
    · intro hx
      have h1 : x ∈ (X.map π).comap π := hx
      rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hzX] at h1
      exact h1
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hc₀i : c₀⁻¹ ∈ oV := inv_mem hc₀
  have hκ : ∀ x : ↥C, (x : G) ∈ Q →
      c₀⁻¹ (c.code ((Quotient.out (π x) : ↥C) : G)) = c₀⁻¹ (c.code (x : G)) := by
    intro x hx
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (zpowers (zC z)) x
    have hw' : ((w : ↥C) : G) ∈ zpowers z := mem_zpowers_zC.mp w.2
    have e : (Quotient.out (π x) : ↥C) = x * w := hw
    rw [e, Subgroup.coe_mul, VCode.code_mul_zp hs hx hw']
  have hnorm : ∀ n : ↥C ⧸ zpowers (zC z), n ∈ normalizer ((X.map π : Subgroup _) : Set _) →
      ((Quotient.out n : ↥C) : G) ∈ normalizer (Q : Set G) := by
    intro n hn
    have hπn : π (Quotient.out n) = n := QuotientGroup.out_eq' n
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have h1 : π ⟨g, hQC hg⟩ ∈ X.map π := (hXmem _).2 hg
      have h2 := (mem_normalizer_iff.mp hn _).mp h1
      rw [← hπn, ← map_inv, ← map_mul, ← map_mul] at h2
      exact (hXmem _).1 h2
    · intro hg
      have hgC : g ∈ C := by
        have h3 := C.mul_mem (C.mul_mem (C.inv_mem (Quotient.out n).2) (hQC hg))
          (Quotient.out n).2
        simpa [mul_assoc] using h3
      have h1 : π (Quotient.out n * ⟨g, hgC⟩ * (Quotient.out n)⁻¹) ∈ X.map π :=
        (hXmem _).2 (by simpa using hg)
      rw [map_mul, map_mul, map_inv, hπn] at h1
      exact (hXmem _).1 ((mem_normalizer_iff.mp hn _).mpr h1)
  refine ⟨fun x => c₀⁻¹ (c.code ((Quotient.out x : ↥C) : G)),
    fun n => if hn : ((Quotient.out n : ↥C) : G) ∈ normalizer (Q : Set G) then
      c₀⁻¹ * c.rho hs ⟨_, hn⟩ * c₀ else 1, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hx' : (x : G) ∈ Q := hx
    have hy' : (y : G) ∈ Q := hy
    rw [← map_mul, hκ (x * y) (mul_mem hx' hy'), hκ x hx', hκ y hy', Subgroup.coe_mul,
      VCode.code_mul hs hx' hy']
    exact hc₀i.1 _ _
  · rintro _ ⟨x, hx, rfl⟩ h0
    have hx' : (x : G) ∈ Q := hx
    rw [hκ x hx'] at h0
    have h1 : c.code (x : G) = 0 := by
      have := congrArg c₀ h0
      rwa [perm_apply_inv_self, hc₀.map_zero] at this
    rw [VCode.code_eq_zero_iff hs hx'] at h1
    rw [← MonoidHom.mem_ker, hker]
    exact mem_zpowers_zC.mpr h1
  · intro v
    refine ⟨π ⟨c.rep (c₀ v), hQC (c.rep_mem _)⟩, (hXmem _).2 (c.rep_mem _), ?_⟩
    rw [hκ _ (c.rep_mem _)]
    show c₀⁻¹ (c.code (c.rep (c₀ v))) = v
    rw [VCode.code_rep hs, perm_inv_apply_self]
  · intro n hn
    rw [dite_eq_left (hnorm n hn)]
    exact hN _
  · rintro n hn _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ Q := hx
    have hnN := hnorm n hn
    have hπn : π (Quotient.out n) = n := QuotientGroup.out_eq' n
    rw [dite_eq_left hnN]
    conv_lhs => rw [← hπn]
    rw [← map_inv, ← map_mul, ← map_mul]
    have hconj : ((Quotient.out n * x * (Quotient.out n)⁻¹ : ↥C) : G) ∈ Q := by
      simpa using VCode.conj_mem_Q hnN hx'
    rw [hκ _ hconj, hκ x hx']
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_apply_inv_self]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [VCode.code_conj hs hnN hx']
    rfl

end Coord

theorem step48NoTim_of
    (h44 : Step44ii) (hNX : Sec4NXModel) : Step48NoTim := by
  intro G _ _ A R g E F S₁ Q z hQ h
  obtain ⟨c, hs, c₀, hc₀, hN, -⟩ := step47_rho_nstar h44 hNX hQ
  obtain ⟨κ, δ, hκ⟩ := exists_nstarCoord hQ.Q_le_centralizer c hs hc₀ hN
  exact hκ.not_tim77 (N48.facts_of N48.n48_check) h

theorem step48_of_tim77
    (hT : Tim77Lemma24) (h44 : Step44ii) (hNX : Sec4NXModel) : Step48 :=
  step48_of hT (step48NoTim_of h44 hNX)

end CFSG.ComponentClassification.AS81

