module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OFix

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace E3S3O

theorem map_eq_of_forall_eq {H : Type*} [Group H] (f : H ≃* H) {A : Subgroup H}
    (hf : ∀ m ∈ A, f m = m) : A.map f.toMonoidHom = A := by
  ext m
  constructor
  · rintro ⟨m', hm', rfl⟩
    rw [show f.toMonoidHom m' = m' from hf m' hm']
    exact hm'
  · intro hm
    exact ⟨m, hm, hf m hm⟩

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)} {x : G}

theorem exists_conj_normalizer_of_fixed (h : TypeRFam r Ω) {s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1) {J₀ : Subgroup G}
    (hJ₀ : XMem Ω x J₀) (hfix : ∀ m ∈ secImg Ω x J₀, secAct h.hyp.conjInvariant hs m = m)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTY : T ≤ layerY Ω x)
    (hTs : T ≤ Subgroup.centralizer ({s} : Set G))
    (hTN : ∀ τ (hτ : τ ∈ T), QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))
      ⟨τ, hTY hτ⟩ ∈ Subgroup.normalizer (secImg Ω x J₀ : Set (SecQuot Ω x))) :
    ∃ n ∈ oddCoreOf (layerY Ω x), T ≤ Subgroup.normalizer (conjSub n J₀ : Set G) ∧
      ∃ Q, IsSylow2In Q (conjSub n J₀) ∧ Q ≤ Subgroup.centralizer ({x} : Set G) ∧
        Q ≤ Subgroup.centralizer ({s} : Set G) := by
  have hcl := h.hyp.conjInvariant
  have hs2' : IsPGroup 2 (Subgroup.zpowers s) := Balance.isPGroup_zpowers_of_mul_self_eq_one hs2
  let St : Subgroup G :=
    { carrier := {v | v ∈ Subgroup.centralizer ({x} : Set G) ∧
        secImg Ω x (conjSub v J₀) = secImg Ω x J₀}
      one_mem' := ⟨Subgroup.one_mem _, by rw [conjSub_one]⟩
      mul_mem' := by
        rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rw [conjSub_mul, secImg_conjSub_eq_map hcl ha, eb, ← secImg_conjSub_eq_map hcl ha, ea]
      inv_mem' := by
        rintro a ⟨ha, ea⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        apply Subgroup.map_injective (f := (secAct hcl ha).toMonoidHom) (secAct hcl ha).injective
        rw [← secImg_conjSub_eq_map hcl ha, ← secImg_conjSub_eq_map hcl ha, ← conjSub_mul,
          mul_inv_cancel, conjSub_one, ea] }
  have hTSt : T ≤ St := fun τ hτ => by
    refine ⟨layerY_le_centralizer (hTY hτ), ?_⟩
    rw [← conjSub_secImg ⟨τ, hTY hτ⟩ J₀]
    exact mem_normalizer_iff_conjSub_eq.mp (hTN τ hτ)
  have hsSt : s ∈ St := ⟨hs, by rw [secImg_conjSub_eq_map hcl hs, map_eq_of_forall_eq _ hfix]⟩
  set V : Subgroup G := T ⊔ Subgroup.zpowers s with hVdef
  have hVSt : V ≤ St := sup_le hTSt (Subgroup.zpowers_le.mpr hsSt)
  have hTn : T ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G) :=
    (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr
      fun τ hτ => Subgroup.mem_centralizer_singleton_iff.mp (hTs hτ)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hV2 : IsPGroup 2 V := IsPGroup.to_sup_of_normal_right' hT2 hs2' hTn
  have hVN : V ≤ Subgroup.normalizer (oddCoreOf (layerY Ω x) : Set G) := fun v hv => by
    obtain ⟨hvx, -⟩ := hVSt hv
    exact mem_normalizer_oddCore_of_mem_normalizer (mem_normalizer_layerY hcl hvx)
  have hperm : ∀ v ∈ V, ∃ n ∈ oddCoreOf (layerY Ω x), conjSub v J₀ = conjSub n J₀ := by
    intro v hv
    obtain ⟨hvx, ev⟩ := hVSt hv
    obtain ⟨ν, hν, hνM⟩ := exists_conj_of_secImg_eq h hJ₀ (XMem.conj' hcl hJ₀ hvx) ev.symm
    exact ⟨ν, mem_oddCoreOf_iff.mpr ⟨ν.2, hν⟩, hνM⟩
  obtain ⟨n, hn, hnN⟩ :=
    exists_conj_normalizer_of_perm (oddCoreOf_odd_natCard _) J₀ hV2 hVN hperm
  obtain ⟨hnY, hnO⟩ := mem_oddCoreOf_iff.mp hn
  have hM := XMem.conj' hcl hJ₀ (layerY_le_centralizer hnY)
  have himg : secImg Ω x (conjSub n J₀) = secImg Ω x J₀ :=
    secImg_conj_of_mem (ν := ⟨n, hnY⟩) hnO J₀
  refine ⟨n, hn, le_sup_left.trans hnN, ?_⟩
  exact exists_sylow_le_centralizer_of_fixed h hs hs2' hM
    (hnN (le_sup_right (a := T) (Subgroup.mem_zpowers s))) (by rw [himg]; exact hfix)

theorem exists_sylow_coreAt_of_isSylow2In {M : Subgroup G} (hM : XMem Ω x M)
    {Pb : Subgroup (SecQuot Ω x)} (hPb : IsSylow2In Pb (secImg Ω x M)) :
    ∃ T, IsSylow2In T (coreAt x M) ∧
      (T.subgroupOf (layerY Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Pb := by
  have hLY : coreAt x M ≤ layerY Ω x := coreAt_le_layerY hM
  obtain ⟨T₀, hT₀, -⟩ :=
    IsSylow2In.exists_ge (P := coreAt x M) (IsPGroup.of_bot (p := 2)) bot_le
  have hT₀' := isSylow2In_map_mk odd_natCard_oddCore_layerY (hT₀.subgroupOf hLY)
  obtain ⟨c, hc, hcP⟩ := S1916.IsSylow2In.exists_conj hT₀' hPb
  obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc
  have hc₀M : (c₀ : G) ∈ coreAt x M := Subgroup.mem_subgroupOf.mp hc₀
  refine ⟨conjSub (c₀ : G) T₀, ?_, ?_⟩
  · have h1 := hT₀.conj (c₀ : G)
    rwa [conjSub_eq_self_of_mem hc₀M] at h1
  · rw [← conjSub_subgroupOf, AscQuot.map_conjSub]
    exact hcP

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
