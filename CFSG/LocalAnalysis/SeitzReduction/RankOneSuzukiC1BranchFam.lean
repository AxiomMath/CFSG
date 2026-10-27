module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchAffine
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchTc

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

variable {G : Type*} [Group G] {K : Type*} [Field K] {T₁ : Subgroup G} {a : ℕ} {d : G}
  {u v : G → K} {κ : K}

@[expose] noncomputable def szSec (hc : SzRootCoords T₁ a d u v κ) (c : K) : G :=
  (hc.surj c 0).choose

theorem szSec_mem (hc : SzRootCoords T₁ a d u v κ) (c : K) : szSec hc c ∈ T₁ :=
  (hc.surj c 0).choose_spec.1

theorem szSec_u (hc : SzRootCoords T₁ a d u v κ) (c : K) : u (szSec hc c) = c :=
  (hc.surj c 0).choose_spec.2.1

@[expose] noncomputable def szFam (U₁ : Subgroup G) (t : G) (hc : SzRootCoords T₁ a d u v κ)
    (c : K) : Subgroup G :=
  U₁ ⊓ centralizer ({szSec hc c * t} : Set G)

theorem map_conj_inf_centralizer {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G))
    (x : G) : (H ⊓ centralizer ({x} : Set G)).map (MulAut.conj n).toMonoidHom =
      H ⊓ centralizer ({n * x * n⁻¹} : Set G) := by
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_inf,
    mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, ⟨hyH, hyx⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.mp hn y).mp hyH, ?_⟩
    calc n * y * n⁻¹ * (n * x * n⁻¹) = n * (y * x) * n⁻¹ := by group
      _ = n * (x * y) * n⁻¹ := by rw [hyx]
      _ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
  · rintro ⟨hzH, hzx⟩
    have hz' := (mem_normalizer_iff.mp (inv_mem hn) z).mp hzH
    rw [inv_inv] at hz'
    refine ⟨n⁻¹ * z * n, ⟨hz', ?_⟩, by group⟩
    calc n⁻¹ * z * n * x = n⁻¹ * (z * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * z) * n := by rw [hzx]
      _ = x * (n⁻¹ * z * n) := by group

end SzC1

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}
  {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}

section Fam

variable (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem fam_injective (hμ : U₁ ≤ centralizer (V : Set G)) :
    Function.Injective (SzC1.szFam U₁ t hc) := fun c c' heq => by
  have e := h.u_eq_of_cent_eq hK hc hμ (SzC1.szSec_mem hc c) (SzC1.szSec_mem hc c') heq
  rwa [SzC1.szSec_u hc c, SzC1.szSec_u hc c'] at e

theorem fam_zero (hμ : U₁ ≤ centralizer (V : Set G)) : SzC1.szFam U₁ t hc 0 = szT₁ L T :=
  (h.T₁_eq_cent hK hc hμ (SzC1.szSec_mem hc 0) (SzC1.szSec_u hc 0)).symm

theorem u_eq_of_mul_eq {y y' r r' : G} (hy : y ∈ szT₁ L T) (hy' : y' ∈ szT₁ L T) (hr : r ∈ V)
    (hr' : r' ∈ V) (e : y * r = y' * r') : u y = u y' := by
  have hA : y'⁻¹ * y ∈ szA₁ (szT₁ L T) := by
    rw [← h.inf_eq_szA₁]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hy') hy, ?_⟩
    rw [show y'⁻¹ * y = r' * r⁻¹ by
      calc y'⁻¹ * y = y'⁻¹ * (y * r) * r⁻¹ := by group
        _ = y'⁻¹ * (y' * r') * r⁻¹ := by rw [e]
        _ = r' * r⁻¹ := by group]
    exact mul_mem hr' (inv_mem hr)
  have hu := hc.u_eq_zero_of_mem_szA₁ h.ha (h.card_K hK hc) hA
  rw [(hc.mul _ (inv_mem hy') _ hy).1, (hc.inv hy').1] at hu
  linear_combination hu - u y' * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem normalizer_U_le_normalizer_U₁ (hμ : U₁ ≤ centralizer (V : Set G)) :
    normalizer (U : Set G) ≤ normalizer (U₁ : Set G) := fun _ hn =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
    have := h.conj_mem_U₁_of_normalizer hμ (inv_mem hn) hw
    rwa [inv_inv] at this

theorem map_conj_fam (hμ : U₁ ≤ centralizer (V : Set G)) {n : G}
    (hn : n ∈ normalizer (U : Set G)) {c : K} {y' r y₀ w : G} (hy' : y' ∈ szT₁ L T) (hr : r ∈ V)
    (hyr : n * SzC1.szSec hc c * n⁻¹ = y' * r) (hy₀ : y₀ ∈ szT₁ L T)
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hx : n * t * n⁻¹ = y₀ * w * t) :
    (SzC1.szFam U₁ t hc c).map (MulAut.conj n).toMonoidHom =
      SzC1.szFam U₁ t hc (u y' + u y₀) := by
  rw [SzC1.szFam, SzC1.map_conj_inf_centralizer (h.normalizer_U_le_normalizer_U₁ hK hc hμ hn)]
  have e : n * (SzC1.szSec hc c * t) * n⁻¹ = (y' * y₀) * (r * w) * t := by
    calc n * (SzC1.szSec hc c * t) * n⁻¹ = (n * SzC1.szSec hc c * n⁻¹) * (n * t * n⁻¹) := by group
      _ = y' * (r * y₀) * w * t := by rw [hyr, hx]; group
      _ = y' * (y₀ * r) * w * t := by rw [h.V_comm hr hy₀]
      _ = (y' * y₀) * (r * w) * t := by group
  rw [e, SzC1.szFam, ← mul_one (SzC1.szSec hc (u y' + u y₀))]
  exact h.cent_eq_of_u_eq hK hc hμ (mul_mem hy' hy₀) (SzC1.szSec_mem hc _)
    (by rw [SzC1.szSec_u hc, (hc.mul _ hy' _ hy₀).1])
    (mul_mem (h.V_le_V₁ hr) hw) (one_mem _)


theorem exists_conj_decomp (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {n : G}
    (hn : n ∈ normalizer (U : Set G)) {y : G} (hy : y ∈ szT₁ L T) :
    ∃ y' ∈ szT₁ L T, ∃ r ∈ V, n * y * n⁻¹ = y' * r :=
  h.exists_mul_of_mem_sup (h.conj_mem_sup_of_normalizer hK hc hμ hlam hn hy)

theorem fam_invariant
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    ∀ n ∈ normalizer (U : Set G), ∀ c : K, ∃ c' : K,
      (SzC1.szFam U₁ t hc c).map (MulAut.conj n).toMonoidHom = SzC1.szFam U₁ t hc c' := by
  intro n hn c
  obtain ⟨y', hy', r, hr, hyr⟩ := h.exists_conj_decomp hK hc hμ hlam hn (SzC1.szSec_mem hc c)
  obtain ⟨y₀, hy₀, w, hw, hx, -⟩ := h.map_conj_T₁_eq hK hc hμ hlam hn
  exact ⟨_, h.map_conj_fam hK hc hμ hn hy' hr hyr hy₀ hw hx⟩

noncomputable def famPerm
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) :
    normalizer (U : Set G) →* Equiv.Perm K :=
  SzC1.familyPerm (SzC1.szFam U₁ t hc) (h.fam_invariant hK hc hμ hlam) (h.fam_injective hK hc hμ)

theorem famPerm_spec
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G))
    (c : K) : (SzC1.szFam U₁ t hc c).map (MulAut.conj (n : G)).toMonoidHom =
      SzC1.szFam U₁ t hc (h.famPerm hK hc hμ hlam n c) :=
  SzC1.familyPerm_spec _ _ _ n c

theorem famPerm_affine
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G)) :
    ∃ ℓ : K →+ K, ∀ c, h.famPerm hK hc hμ hlam n c = h.famPerm hK hc hμ hlam n 0 + ℓ c := by
  have hK' := h.card_K hK hc
  have hn := n.2
  obtain ⟨y₀, hy₀, w, hw, hx, -⟩ := h.map_conj_T₁_eq hK hc hμ hlam hn
  choose y' hy' r hr hyr using fun c : K =>
    h.exists_conj_decomp hK hc hμ hlam hn (SzC1.szSec_mem hc c)
  have hval : ∀ c, h.famPerm hK hc hμ hlam n c = u (y' c) + u y₀ := fun c =>
    h.fam_injective hK hc hμ
      (((h.famPerm_spec hK hc hμ hlam n c).symm).trans
        (h.map_conj_fam hK hc hμ hn (hy' c) (hr c) (hyr c) hy₀ hw hx))
  have hadd : ∀ c c', u (y' (c + c')) = u (y' c) + u (y' c') := by
    intro c c'
    have hsec := SzC1.szSec_mem hc
    have hA := hc.inv_mul_mem_szA₁_of_u_eq h.ha hK' (mul_mem (hsec c) (hsec c')) (hsec (c + c'))
      (by rw [(hc.mul _ (hsec c) _ (hsec c')).1, SzC1.szSec_u hc, SzC1.szSec_u hc,
        SzC1.szSec_u hc])
    set a₀ := (SzC1.szSec hc c * SzC1.szSec hc c')⁻¹ * SzC1.szSec hc (c + c') with ha₀
    have hA' := h.conj_mem_szA₁_of_normalizer hμ hn hA
    have e1 : SzC1.szSec hc (c + c') = SzC1.szSec hc c * SzC1.szSec hc c' * a₀ := by
      rw [ha₀]; group
    have e2 : (n : G) * SzC1.szSec hc (c + c') * (n : G)⁻¹ =
        (y' c * y' c') * (r c * r c' * ((n : G) * a₀ * (n : G)⁻¹)) := by
      rw [e1]
      calc (n : G) * (SzC1.szSec hc c * SzC1.szSec hc c' * a₀) * (n : G)⁻¹ =
            ((n : G) * SzC1.szSec hc c * (n : G)⁻¹) * ((n : G) * SzC1.szSec hc c' * (n : G)⁻¹) *
              ((n : G) * a₀ * (n : G)⁻¹) := by group
        _ = y' c * (r c * y' c') * r c' * ((n : G) * a₀ * (n : G)⁻¹) := by
            rw [hyr c, hyr c']; group
        _ = y' c * (y' c' * r c) * r c' * ((n : G) * a₀ * (n : G)⁻¹) := by
            rw [h.V_comm (hr c) (hy' c')]
        _ = (y' c * y' c') * (r c * r c' * ((n : G) * a₀ * (n : G)⁻¹)) := by group
    have e3 := h.u_eq_of_mul_eq hK hc (hy' (c + c')) (mul_mem (hy' c) (hy' c')) (hr (c + c'))
      (mul_mem (mul_mem (hr c) (hr c')) (h.le hA')) ((hyr (c + c')).symm.trans e2)
    rw [e3, (hc.mul _ (hy' c) _ (hy' c')).1]
  have h0 : u (y' 0) = 0 := by
    have hA0 := (hc.mem_szA₁_iff h.ha hK' (SzC1.szSec_mem hc 0)).mpr (SzC1.szSec_u hc 0)
    have hA0' := h.conj_mem_szA₁_of_normalizer hμ hn hA0
    have e := h.u_eq_of_mul_eq hK hc (hy' 0) (one_mem _) (hr 0) (h.le hA0')
      ((hyr 0).symm.trans (one_mul _).symm)
    rw [e, hc.u_one]
  refine ⟨AddMonoidHom.mk' (fun c => u (y' c)) hadd, fun c => ?_⟩
  rw [hval, hval, h0, zero_add, AddMonoidHom.mk'_apply]
  ring

end Fam

end SzC1Stage

end CFSG.SeitzReduction.RankOne
