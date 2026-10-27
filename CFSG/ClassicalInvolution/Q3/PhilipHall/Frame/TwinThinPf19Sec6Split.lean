module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf18CrossSetting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

namespace TwinThin

namespace Cross

variable {G : Type} [Group G] {P : Set (Subgroup G)} {m : ℕ}

theorem InducedBy.pow (I : AEIdent P m) {u : G} (hu : u ∈ Subgroup.normalizer (pSpan P : Set G))
    {w : Wr m} (hw : InducedBy I u w) (j : ℕ) : InducedBy I (u ^ j) (w ^ j) := by
  induction j with
  | zero =>
    intro x y hxy
    have : y = x := Subtype.ext (by simpa using hxy)
    subst this
    simp
  | succ j ih =>
    intro x y hxy
    have huj : u ^ j ∈ Subgroup.normalizer (pSpan P : Set G) :=
      (Subgroup.normalizer (pSpan P : Set G)).pow_mem hu j
    have hx' : u ^ j * (x : G) * (u ^ j)⁻¹ ∈ pSpan P :=
      TwinThinPf.conj_mem_of_normalizer huj x.2
    have h1 := ih x ⟨u ^ j * (x : G) * (u ^ j)⁻¹, hx'⟩ rfl
    have h2 := hw ⟨u ^ j * (x : G) * (u ^ j)⁻¹, hx'⟩ y (by
      rw [hxy, pow_succ']
      show _ = u * (u ^ j * (x : G) * (u ^ j)⁻¹) * u⁻¹
      group)
    rw [h2, h1, pow_succ', map_mul]
    group

end Cross

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem exists_mul_mem_inf {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ x ∈ piGen π, x * c ∈ Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  have hJ' : conjSub c (conjSub g K) ∈ π := S.conj_pi_of_cent hc S.hg
  obtain ⟨x, hx, hxJ⟩ := S.trans_pi _ hJ' _ S.hg
  rw [← conjSub_mul] at hxJ
  have hxc : x ∈ Subgroup.centralizer ({z} : Set G) := S.X_le_cent hx
  have hd : x * c ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hxc hc
  have hu : (x * c) * (g * z * g⁻¹) * (x * c)⁻¹ = g * z * g⁻¹ := by
    have h1 := (S.hz.conj g).conj (x * c)
    rw [hxJ] at h1
    exact ((S.hz.conj g).eq h1).symm
  refine ⟨x, hx, hd, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc (x * c) * (g * z * g⁻¹) = ((x * c) * (g * z * g⁻¹) * (x * c)⁻¹) * (x * c) := by group
    _ = (g * z * g⁻¹) * (x * c) := by rw [hu]

theorem no_split {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m) (htw : S.TwinLab m)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) (hcK : conjSub c K = K)
    (hcK' : ∀ k ∈ K', c * k = k * c) (hc3 : ∃ k ∈ K, c * k * c⁻¹ ≠ k)
    (hord : ∃ a : ℕ, c ^ (3 ^ a) = 1) : False := by
  classical
  obtain ⟨x, hxX, hxc⟩ := S.exists_mul_mem_inf hc
  set c' := x * c with hc'
  have hc'g : c' ∈ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := (Subgroup.mem_inf.mp hxc).2
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.1 hk)) x hxX
  have hxK' : ∀ k ∈ K', x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (S.pair_le_cent.2 hk)) x hxX
  have hcmem : ∀ k ∈ K, c * k * c⁻¹ ∈ K := by
    intro k hk
    have := conj_mem_conjSub (n := c) hk
    rwa [hcK] at this
  have hc'K : ∀ k ∈ K, c' * k * c'⁻¹ = c * k * c⁻¹ := by
    intro k hk
    have h1 := hxK _ (hcmem k hk)
    calc c' * k * c'⁻¹ = x * (c * k * c⁻¹) * x⁻¹ := by rw [hc']; group
      _ = (c * k * c⁻¹ * x) * x⁻¹ := by rw [h1]
      _ = c * k * c⁻¹ := by group
  have hc'K' : ∀ k ∈ K', c' * k = k * c' := by
    intro k hk
    rw [hc', mul_assoc, hcK' k hk, ← mul_assoc, hxK' k hk, mul_assoc]
  have hpow : ∀ j : ℕ, ∀ k ∈ K, c' ^ j * k * (c' ^ j)⁻¹ = c ^ j * k * (c ^ j)⁻¹ ∧
      c ^ j * k * (c ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => intro k hk; simpa using hk
    | succ j ih =>
      intro k hk
      obtain ⟨h1, h2⟩ := ih k hk
      have e1 : c' ^ (j + 1) * k * (c' ^ (j + 1))⁻¹ =
          c' * (c' ^ j * k * (c' ^ j)⁻¹) * c'⁻¹ := by
        rw [pow_succ']; group
      have e2 : c ^ (j + 1) * k * (c ^ (j + 1))⁻¹ = c * (c ^ j * k * (c ^ j)⁻¹) * c⁻¹ := by
        rw [pow_succ']; group
      rw [e1, e2, h1]
      exact ⟨hc'K _ h2, hcmem _ h2⟩
  obtain ⟨w, hw⟩ := Cross.exists_induced hm hAut J (S.mem_normalizer_pSpan_fam hc'g)
    (fun L hL => S.fam_conj_of_cent' hc'g hL)
  obtain ⟨α, hα, b, hlab⟩ := J.label K S.mem_fam_self
  have hlab' := htw J hlab
  have hcent : ∀ y ∈ AE.memBar α hα (!b), mkQ m w * y * (mkQ m w)⁻¹ = y := by
    intro y hy
    rw [← hlab'] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hy'K' : (y' : G) ∈ K' := Subgroup.mem_subgroupOf.mp hy'
    exact hw.cent (x := y') (by rw [hc']; exact hc'K' _ hy'K')
  have h4 := TwinThinPf19.pow_four_cent_memBar hm α hα (!b) w hcent b
  have hw4 : Cross.InducedBy J (c' ^ 4) (w ^ 4) :=
    Cross.InducedBy.pow J (S.mem_normalizer_pSpan_fam hc'g) hw 4
  have hK4 : ∀ k ∈ K, c ^ 4 * k * (c ^ 4)⁻¹ = k := by
    intro k hk
    obtain ⟨e1, hmem⟩ := hpow 4 k hk
    have hkX : k ∈ pSpan (fam K (conjSub g (piGen π))) := le_pSpan S.mem_fam_self hk
    have hmX : c ^ 4 * k * (c ^ 4)⁻¹ ∈ pSpan (fam K (conjSub g (piGen π))) :=
      le_pSpan S.mem_fam_self hmem
    have hmem' : c' ^ 4 * k * (c' ^ 4)⁻¹ ∈ K := by rw [e1]; exact hmem
    have hy := hw4 ⟨k, hkX⟩ ⟨c' ^ 4 * k * (c' ^ 4)⁻¹, le_pSpan S.mem_fam_self hmem'⟩ rfl
    have hφk : J.φ ⟨k, hkX⟩ ∈ AE.memBar α hα b := by
      rw [← hlab]
      exact J.mem_map S.mem_fam_self hk
    have h5 := h4 _ hφk
    rw [map_pow] at hy
    rw [h5] at hy
    have := J.injOn hm S.mem_fam_self (S.card8 K S.hK) hlab hmem' hk hy
    rw [← e1]
    exact this
  obtain ⟨a, ha⟩ := hord
  obtain ⟨k, hk, hne⟩ := hc3
  apply hne
  have hF : ∀ j : ℕ, (fun t : G => c * t * c⁻¹)^[j] k = c ^ j * k * (c ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      group
  have hp1 : Function.IsPeriodicPt (fun t : G => c * t * c⁻¹) (3 ^ a) k := by
    show (fun t : G => c * t * c⁻¹)^[3 ^ a] k = k
    rw [hF, ha]; group
  have hp2 : Function.IsPeriodicPt (fun t : G => c * t * c⁻¹) 4 k := by
    show (fun t : G => c * t * c⁻¹)^[4] k = k
    rw [hF]; exact hK4 k hk
  have hp := hp1.gcd hp2
  have hg1 : Nat.gcd (3 ^ a) 4 = 1 := by
    have : Nat.Coprime (3 ^ a) (2 ^ 2) := Nat.Coprime.pow _ _ (by norm_num)
    simpa using this
  rw [hg1] at hp
  exact hp

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
