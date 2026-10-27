module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

open Subgroup

theorem exists_finset_sup_eq_of_normal (𝒜 : Finset (Subgroup G))
    (hAn : ∀ A ∈ 𝒜, A.Normal) (hAs : ∀ A ∈ 𝒜, IsSimpleGroup ↥A)
    (hAnab : ∀ A ∈ 𝒜, ¬ IsMulCommutative ↥A)
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (N : Subgroup G) (hsup : 𝒜.sup id = N) :
    ∀ M : Subgroup G, M ≤ N → (M.subgroupOf N).Normal →
      ∃ s : Finset (Subgroup G), s ⊆ 𝒜 ∧ M = s.sup id := by
  classical
  induction 𝒜 using Finset.induction_on generalizing N with
  | empty =>
      intro M hMN _
      have hNbot : N = ⊥ := by simpa using hsup.symm
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [Finset.sup_empty]
      exact le_bot_iff.mp (hMN.trans (le_of_eq hNbot))
  | insert a s ha ih =>
      intro M hMN hMnorm
      set N₁ : Subgroup G := s.sup id with hN₁def
      have hsup' : a ⊔ N₁ = N := by
        rw [← hsup, Finset.sup_insert, hN₁def]
        rfl
      have ha_mem : a ∈ insert a s := Finset.mem_insert_self a s
      have hAn' : ∀ A ∈ s, A.Normal := fun A hA => hAn A (Finset.mem_insert_of_mem hA)
      have hAs' : ∀ A ∈ s, IsSimpleGroup ↥A := fun A hA => hAs A (Finset.mem_insert_of_mem hA)
      have hAnab' : ∀ A ∈ s, ¬ IsMulCommutative ↥A :=
        fun A hA => hAnab A (Finset.mem_insert_of_mem hA)
      have hcomm' : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → ∀ x ∈ A, ∀ y ∈ B, Commute x y :=
        fun A hA B hB hne => hcomm A (Finset.mem_insert_of_mem hA) B
          (Finset.mem_insert_of_mem hB) hne
      have hN₁_le : N₁ ≤ N := hsup' ▸ le_sup_right
      have ha_le_N : a ≤ N := hsup' ▸ le_sup_left
      have : a.Normal := hAn a ha_mem
      have hcomm_a : ∀ B ∈ s, ∀ x ∈ a, ∀ y ∈ B, Commute x y := by
        intro B hB x hx y hy
        exact hcomm a ha_mem B (Finset.mem_insert_of_mem hB)
          (fun h => ha (h ▸ hB)) x hx y hy
      have ha_cent : a ≤ Subgroup.centralizer (N₁ : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        refine Finset.sup_le fun B hB => ?_
        intro y hy x hx
        exact hcomm_a B hB x hx y hy
      have hcenter_a : Subgroup.center ↥a = ⊥ := by
        have : IsSimpleGroup ↥a := hAs a ha_mem
        have hnab : ∃ x y : ↥a, x * y ≠ y * x := by
          by_contra h
          push Not at h
          exact hAnab a ha_mem ⟨⟨fun x y => h x y⟩⟩
        exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
      have hinf : a ⊓ N₁ = ⊥ := by
        refine le_bot_iff.mp ?_
        rintro z ⟨hza, hzN₁⟩
        have hzcenter : (⟨z, hza⟩ : ↥a) ∈ Subgroup.center ↥a := by
          rw [Subgroup.mem_center_iff]
          intro x
          have hxz : z * (x : G) = (x : G) * z :=
            Subgroup.mem_centralizer_iff.mp (ha_cent x.2) z hzN₁
          exact Subtype.ext hxz.symm
        have hz1 : (⟨z, hza⟩ : ↥a) = 1 :=
          Subgroup.mem_bot.mp (hcenter_a ▸ hzcenter)
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz1)
      by_cases hMN₁ : M ≤ N₁
      ·
        have hnorm : (M.subgroupOf N₁).Normal := by
          rw [Subgroup.normal_subgroupOf_iff hMN₁]
          intro x y hx hy
          exact (Subgroup.normal_subgroupOf_iff hMN).mp hMnorm x y hx (hN₁_le hy)
        obtain ⟨t, ht, hMt⟩ := ih hAn' hAs' hAnab' hcomm' N₁ rfl M hMN₁ hnorm
        exact ⟨t, fun A hA => Finset.mem_insert_of_mem (ht hA), hMt⟩
      ·
        have haM : a ≤ M := by
          by_contra hnot
          have hinfM : a ⊓ M = ⊥ := by
            have : IsSimpleGroup ↥a := hAs a ha_mem
            have hnormAM : ((a ⊓ M).subgroupOf a).Normal := by
              rw [Subgroup.normal_subgroupOf_iff inf_le_left]
              intro h k hh hk
              exact Subgroup.mem_inf.mpr
                ⟨a.mul_mem (a.mul_mem hk hh.1) (a.inv_mem hk),
                  (Subgroup.normal_subgroupOf_iff hMN).mp hMnorm h k hh.2 (ha_le_N hk)⟩
            have := hnormAM
            rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((a ⊓ M).subgroupOf a) with h | h
            · have hd : Disjoint (a ⊓ M) a := Subgroup.subgroupOf_eq_bot.mp h
              have h1 := disjoint_iff.mp hd
              rwa [inf_of_le_left inf_le_left] at h1
            · exact absurd ((Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right) hnot
          obtain ⟨m, hmM, hmN₁⟩ := Set.not_subset.mp hMN₁
          have hmN : m ∈ a ⊔ N₁ := hsup' ▸ hMN hmM
          obtain ⟨a', ha', n, hn, hmn⟩ :=
            (Subgroup.mem_sup_of_normal_left (s := a) (t := N₁)).mp hmN
          have ha'ne : a' ≠ 1 := by
            rintro rfl
            have hmn' : m = n := by simpa using hmn.symm
            exact hmN₁ (hmn' ▸ hn)
          have hcomm_zero : ∀ x ∈ a, x * (a' : G) * x⁻¹ * (a' : G)⁻¹ = 1 := by
            intro x hx
            have hxn : x * n = n * x := by
              have h1 : x ∈ Subgroup.centralizer (N₁ : Set G) := ha_cent hx
              exact ((Subgroup.mem_centralizer_iff.mp h1) n hn).symm
            have e : x * m * x⁻¹ * m⁻¹ = x * a' * x⁻¹ * (a' : G)⁻¹ := by
              rw [← hmn]
              have h2 : n * x⁻¹ = x⁻¹ * n := (show Commute n x from hxn.symm).inv_right.eq
              calc x * (a' * n) * x⁻¹ * (a' * n)⁻¹
                  = x * a' * (n * x⁻¹) * (n⁻¹ * a'⁻¹) := by group
                _ = x * a' * (x⁻¹ * n) * (n⁻¹ * a'⁻¹) := by rw [h2]
                _ = x * a' * x⁻¹ * a'⁻¹ := by group
            have hmemA : x * m * x⁻¹ * m⁻¹ ∈ a := by
              rw [e]
              exact a.mul_mem (a.mul_mem (a.mul_mem hx ha') (a.inv_mem hx)) (a.inv_mem ha')
            have hmemM : x * m * x⁻¹ * m⁻¹ ∈ M := by
              have hxN : x ∈ N := hsup' ▸ Subgroup.mem_sup_left hx
              have hxm : x * m * x⁻¹ ∈ M :=
                (Subgroup.normal_subgroupOf_iff hMN).mp hMnorm m x hmM hxN
              exact M.mul_mem hxm (M.inv_mem hmM)
            have h1 := Subgroup.mem_inf.mpr ⟨hmemA, hmemM⟩
            rw [hinfM] at h1
            exact e.symm.trans (Subgroup.mem_bot.mp h1)
          have hcent : (⟨a', ha'⟩ : ↥a) ∈ Subgroup.center ↥a := by
            rw [Subgroup.mem_center_iff]
            intro x
            have h1 := hcomm_zero x x.2
            have h2 : x * a' * x⁻¹ = a' := by
              have h3 : x * a' * x⁻¹ * a'⁻¹ = 1 := h1
              calc x * a' * x⁻¹ = x * a' * x⁻¹ * a'⁻¹ * a' := by group
                _ = a' := by rw [h3, one_mul]
            exact Subtype.ext (by
              have h3 : (x : G) * a' = a' * (x : G) := by
                have h4 := congrArg (fun z => z * (x : G)) h2
                simpa [mul_assoc] using h4
              exact h3)
          have : (⟨a', ha'⟩ : ↥a) = 1 :=
            Subgroup.mem_bot.mp (hcenter_a ▸ hcent)
          exact ha'ne (congrArg Subtype.val this)
        have hnormP : ((M ⊓ N₁).subgroupOf N₁).Normal := by
          rw [Subgroup.normal_subgroupOf_iff inf_le_right]
          intro x y hx hy
          refine Subgroup.mem_inf.mpr ⟨?_, N₁.mul_mem (N₁.mul_mem hy hx.2) (N₁.inv_mem hy)⟩
          exact (Subgroup.normal_subgroupOf_iff hMN).mp hMnorm x y hx.1 (hN₁_le hy)
        obtain ⟨t, ht, hMt⟩ := ih hAn' hAs' hAnab' hcomm' N₁ rfl (M ⊓ N₁) inf_le_right hnormP
        refine ⟨insert a t, ?_, ?_⟩
        · intro A hA
          rcases Finset.mem_insert.mp hA with rfl | hA
          · exact ha_mem
          · exact Finset.mem_insert_of_mem (ht hA)
        · rw [Finset.sup_insert, ← hMt]
          refine le_antisymm ?_ (sup_le haM inf_le_left)
          intro z hz
          have hzN : z ∈ N := hMN hz
          have hzN' : z ∈ a ⊔ N₁ := hsup' ▸ hzN
          obtain ⟨b, hb, c, hc, hbc⟩ :=
            (Subgroup.mem_sup_of_normal_left (s := a) (t := N₁)).mp hzN'
          have hbM : b ∈ M := haM hb
          have hcM : c ∈ M := by
            have hcz : c = b⁻¹ * z := by rw [← hbc]; group
            rw [hcz]
            exact M.mul_mem (M.inv_mem hbM) hz
          rw [← hbc]
          exact Subgroup.mul_mem _
            (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hcM, hc⟩))

theorem eq_of_isComponent_sup_of_direct [Finite G] (𝒜 : Finset (Subgroup G))
    (hAn : ∀ A ∈ 𝒜, A.Normal) (hAs : ∀ A ∈ 𝒜, IsSimpleGroup ↥A)
    (hAnab : ∀ A ∈ 𝒜, ¬ IsMulCommutative ↥A)
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hsup : 𝒜.sup id = ⊤) :
    ∀ L : Subgroup G, CFSG.IsComponent L → ∃ A ∈ 𝒜, L = A := by
  classical
  have hcomp : ∀ A ∈ 𝒜, CFSG.IsComponent A := by
    intro A hA
    have : IsSimpleGroup ↥A := hAs A hA
    have hnab : ∃ x y : ↥A, x * y ≠ y * x := by
      by_contra h
      push Not at h
      exact hAnab A hA ⟨⟨fun x y => h x y⟩⟩
    refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1, ?_⟩
    exact (hAn A hA).isSubnormal
  have hE : CFSG.layer G = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact Finset.sup_le fun A hA => CFSG.LocalCores.component_le_layer (hcomp A hA)
  intro L hL
  have hLn : L.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hE hL
  obtain ⟨s, hs, hLs⟩ := exists_finset_sup_eq_of_normal 𝒜 hAn hAs hAnab hcomm ⊤ hsup
    L le_top (hLn.subgroupOf ⊤)
  have hsub : s ⊆ 𝒜 := hs
  have htwo : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → False := by
    intro A hA B hB hne
    have hAle : A ≤ L := by
      rw [hLs]
      exact Finset.le_sup (f := id) hA
    have hBle : B ≤ L := by
      rw [hLs]
      exact Finset.le_sup (f := id) hB
    have hAnL : (A.subgroupOf L).Normal := (hAn A (hsub hA)).subgroupOf L
    have hBnL : (B.subgroupOf L).Normal := (hAn B (hsub hB)).subgroupOf L
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
    let f : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' _
    have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
    have hAn' : (A.subgroupOf L).map f = ⊤ := by
      have : ((A.subgroupOf L).map f).Normal := hAnL.map f hfs
      rcases Subgroup.Normal.eq_bot_or_eq_top ((A.subgroupOf L).map f) with h | h
      · exfalso
        have hle : A.subgroupOf L ≤ Subgroup.center ↥L := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L)]
          exact (Subgroup.map_eq_bot_iff _).mp h
        have hAab : IsMulCommutative ↥A := by
          refine IsMulCommutative.of_comm fun u v => ?_
          apply Subtype.ext
          have huL : (⟨(u : G), hAle u.2⟩ : ↥L) ∈ A.subgroupOf L :=
            Subgroup.mem_subgroupOf.mpr u.2
          have h1 := Subgroup.mem_center_iff.mp (hle huL) (⟨(v : G), hAle v.2⟩ : ↥L)
          exact (congrArg Subtype.val h1).symm
        exact hAnab A (hsub hA) hAab
      · exact h
    have hBn' : (B.subgroupOf L).map f = ⊤ := by
      have : ((B.subgroupOf L).map f).Normal := hBnL.map f hfs
      rcases Subgroup.Normal.eq_bot_or_eq_top ((B.subgroupOf L).map f) with h | h
      · exfalso
        have hle : B.subgroupOf L ≤ Subgroup.center ↥L := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L)]
          exact (Subgroup.map_eq_bot_iff _).mp h
        have hBab : IsMulCommutative ↥B := by
          refine IsMulCommutative.of_comm fun u v => ?_
          apply Subtype.ext
          have huL : (⟨(u : G), hBle u.2⟩ : ↥L) ∈ B.subgroupOf L :=
            Subgroup.mem_subgroupOf.mpr u.2
          have h1 := Subgroup.mem_center_iff.mp (hle huL) (⟨(v : G), hBle v.2⟩ : ↥L)
          exact (congrArg Subtype.val h1).symm
        exact hAnab B (hsub hB) hBab
      · exact h
    have hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b :=
      hcomm A (hsub hA) B (hsub hB) hne
    obtain ⟨x, y, hxy⟩ := hL.1.2.2
    have hxmem : x ∈ (A.subgroupOf L).map f := by rw [hAn']; exact Subgroup.mem_top x
    have hymem : y ∈ (B.subgroupOf L).map f := by rw [hBn']; exact Subgroup.mem_top y
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hxmem
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hymem
    have hab : f a * f b = f b * f a := by
      have habL : a * b = b * a := by
        apply Subtype.ext
        exact (hcommAB _ (Subgroup.mem_subgroupOf.mp ha) _
          (Subgroup.mem_subgroupOf.mp hb)).eq
      calc f a * f b = f (a * b) := (map_mul f a b).symm
        _ = f (b * a) := by rw [habL]
        _ = f b * f a := map_mul f b a
    exact hxy (by rw [← hax, ← hby]; exact hab)
  have hsingle : ∃ A ∈ s, s = {A} := by
    rcases Finset.eq_empty_or_nonempty s with h | ⟨A, hA⟩
    · exfalso
      have hLbot : L = ⊥ := by rw [hLs, h, Finset.sup_empty]
      have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
      exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt hLbot
    · refine ⟨A, hA, ?_⟩
      ext B
      constructor
      · intro hB
        have hBA : B = A := by
          by_contra hne
          exact htwo B hB A hA hne
        rw [hBA]
        exact Finset.mem_singleton_self A
      · intro hB
        rw [Finset.mem_singleton.mp hB]
        exact hA
  obtain ⟨A, hA, hsA⟩ := hsingle
  refine ⟨A, hsub hA, ?_⟩
  rw [hLs, hsA, Finset.sup_singleton]
  rfl

theorem eq_of_isComponentOf_sup_of_direct [Finite G] {N : Subgroup G}
    (𝒜 : Finset (Subgroup G)) (hAle : ∀ A ∈ 𝒜, A ≤ N)
    (hAn : ∀ A ∈ 𝒜, (A.subgroupOf N).Normal)
    (hAs : ∀ A ∈ 𝒜, IsSimpleGroup ↥A)
    (hAnab : ∀ A ∈ 𝒜, ¬ IsMulCommutative ↥A)
    (hcomm : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    (hsup : 𝒜.sup id = N) :
    ∀ L : Subgroup G, CFSG.Open.IsComponentOf L N → ∃ A ∈ 𝒜, L = A := by
  classical
  intro L hL
  set g : Subgroup G → Subgroup ↥N := fun A => A.subgroupOf N with hg
  set 𝒜N : Finset (Subgroup ↥N) := 𝒜.image g with h𝒜N
  have hAnN : ∀ B ∈ 𝒜N, B.Normal := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    exact hAn A hA
  have hAsN : ∀ B ∈ 𝒜N, IsSimpleGroup ↥B := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    have : IsSimpleGroup ↥A := hAs A hA
    exact (Subgroup.subgroupOfEquivOfLe (hAle A hA)).isSimpleGroup
  have hAnabN : ∀ B ∈ 𝒜N, ¬ IsMulCommutative ↥B := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    exact fun h => hAnab A hA ((CFSG.SignalizerFunctorTheorem.McBride.isMulCommutative_congr
      (Subgroup.subgroupOfEquivOfLe (hAle A hA))).mp h)
  have hcommN : ∀ B ∈ 𝒜N, ∀ C ∈ 𝒜N, B ≠ C → ∀ a ∈ B, ∀ b ∈ C, Commute a b := by
    intro B hB C hC hne a ha b hb
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    have hAD : A ≠ D := by
      rintro rfl
      exact hne rfl
    exact Subtype.ext (hcomm A hA D hD hAD _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)).eq
  have hsupg : 𝒜.sup g = ⊤ := by
    have hmap : (𝒜.sup g).map N.subtype = 𝒜.sup id := by
      calc (𝒜.sup g).map N.subtype = (⨆ A, ⨆ (_ : A ∈ 𝒜), g A).map N.subtype := by
            rw [Finset.sup_eq_iSup]
        _ = ⨆ A, ⨆ (_ : A ∈ 𝒜), (g A).map N.subtype := by
              rw [Subgroup.map_iSup]
              simp only [Subgroup.map_iSup]
        _ = ⨆ A, ⨆ (_ : A ∈ 𝒜), A := by
              refine iSup_congr fun A => iSup_congr fun hA => ?_
              exact Subgroup.map_subgroupOf_eq_of_le (hAle A hA)
        _ = 𝒜.sup id := (Finset.sup_eq_iSup ..).symm
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hmap.trans hsup
  have hsupN : 𝒜N.sup id = ⊤ := by
    rw [h𝒜N, Finset.sup_image]
    exact hsupg
  have hLc : CFSG.IsComponent (L.subgroupOf N) := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL.1).mp ?_
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L N).mpr hL
  obtain ⟨B, hB, hBL⟩ := CFSG.GroupTheory.eq_of_isComponent_sup_of_direct 𝒜N hAnN hAsN hAnabN
    hcommN hsupN (L.subgroupOf N) hLc
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  refine ⟨A, hA, ?_⟩
  have hmap := congrArg (Subgroup.map N.subtype) hBL
  rwa [Subgroup.map_subgroupOf_eq_of_le (hAle A hA), Subgroup.map_subgroupOf_eq_of_le hL.1]
    at hmap

end CFSG.GroupTheory
