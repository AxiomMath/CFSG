module

public import CFSG.Certificates.Kernel.Fin76bOm.Restrict
public import CFSG.Certificates.Kernel.Fin76bOm.TwinSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentModel

public section

namespace CFSG.KC.Fin76bOm

open Equiv Subgroup CFSG.EvenSporadicStandard.Fin76b

section Roots

variable {G : Type*} [Group G]

theorem map_rootGroup_inclusion {X C : Subgroup G} (hCX : C ≤ X) {t : G} (htC : t ∈ C)
    (hroot : ∀ x ∈ X, x * x = t → x ∈ C) :
    (rootGroup ↥C ⟨t, htC⟩).map (inclusion hCX) = rootGroup ↥X ⟨t, hCX htC⟩ := by
  unfold rootGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Set.mem_setOf_eq, ← map_mul, hc]
    rfl
  · intro hx
    have hx' : (x : G) * x = t := congrArg Subtype.val hx
    refine ⟨⟨x, hroot x x.2 hx'⟩, Subtype.ext hx', rfl⟩

theorem eLabelling_of_inclusion {X C : Subgroup G} (hCX : C ≤ X) {t : G} (htC : t ∈ C)
    (hroot : ∀ x ∈ X, x * x = t → x ∈ C) {M : ℕ → ℕ → ℕ} {tI : ℕ} {elt : ℕ → ↥C}
    (h : ELabelling (rootGroup ↥C ⟨t, htC⟩) ⟨t, htC⟩ M tI elt) :
    ELabelling (rootGroup ↥X ⟨t, hCX htC⟩) ⟨t, hCX htC⟩ M tI
      (fun a => inclusion hCX (elt a)) := by
  have := h.map (inclusion hCX) (inclusion_injective hCX)
  rwa [map_rootGroup_inclusion hCX htC hroot] at this

theorem eLabelling_congr {E : Subgroup G} {t : G} {M M' : ℕ → ℕ → ℕ} {tI : ℕ} {elt : ℕ → G}
    (h : ELabelling E t M tI elt) (hM : ∀ a < 32, ∀ b < 32, M a b = M' a b) :
    ELabelling E t M' tI elt where
  mem := h.mem
  surj := h.surj
  inj := h.inj
  lt a ha b hb := hM a ha b hb ▸ h.lt a ha b hb
  mul a ha b hb := hM a ha b hb ▸ h.mul a ha b hb
  one := h.one
  tI_lt := h.tI_lt
  at_tI := h.at_tI

theorem rootSet_eq_of_cent {X C : Subgroup G} {t : G} (hC : C = X ⊓ centralizer ({t} : Set G)) :
    rootSet X t = rootSet C t := by
  ext x
  constructor
  · rintro ⟨hx, hxx⟩
    refine ⟨?_, hxx⟩
    rw [hC]
    exact ⟨hx, mem_centralizer_singleton_iff.2 (by rw [← hxx, mul_assoc])⟩
  · rintro ⟨hx, hxx⟩
    rw [hC] at hx
    exact ⟨hx.1, hxx⟩

theorem rootFactsFor_of_cent {X C : Subgroup G} {t : G} (hC : C = X ⊓ centralizer ({t} : Set G))
    (htC : t ∈ C) (htX : t ∈ X) (h : RootFactsFor ↥C ⟨t, htC⟩) : RootFactsFor ↥X ⟨t, htX⟩ := by
  have hCX : C ≤ X := by
    rw [hC]
    exact inf_le_left
  have hcen : ∀ c ∈ C, c * t = t * c := fun c hc => by
    rw [hC] at hc
    exact mem_centralizer_singleton_iff.1 hc.2
  have hR := rootSet_eq_of_cent hC
  refine RootFactsFor.of_ambient htX ?_ ?_ ?_ ?_ ?_
  · rw [← hC]
    have h1 := h.card_cent
    have htop : centralizer ({(⟨t, htC⟩ : ↥C)} : Set ↥C) = ⊤ := by
      rw [eq_top_iff]
      intro c _
      exact mem_centralizer_singleton_iff.2 (Subtype.ext (hcen c c.2))
    rw [htop, Subgroup.card_top] at h1
    exact h1
  · rw [hR, ← image_val_roots htC, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact h.roots_le
  · rw [hR, ← map_rootGroup htC, Subgroup.card_map_of_injective C.subtype_injective]
    exact h.card_E
  · intro l hlX hl
    have hne : ∃ r : ↥C, r * r = ⟨t, htC⟩ := by
      by_contra hno'
      have hno : ∀ r : ↥C, r * r ≠ ⟨t, htC⟩ := fun r hr => hno' ⟨r, hr⟩
      have hE : rootGroup ↥C ⟨t, htC⟩ = ⊥ := by
        rw [rootGroup, closure_eq_bot_iff]
        intro x hx
        exact absurd hx (hno x)
      have h32 := h.card_E
      rw [hE, Subgroup.card_bot] at h32
      omega
    obtain ⟨r, hr⟩ := hne
    have hr' : (r : G) * r = t := congrArg Subtype.val hr
    have hlr := hl r (hCX r.2) hr'
    have hlt : l * t = t * l := by
      rw [← hr']
      calc l * (↑r * ↑r) = (l * r) * r := by rw [mul_assoc]
        _ = (r * l) * r := by rw [hlr]
        _ = r * (l * r) := by rw [mul_assoc]
        _ = r * (r * l) := by rw [hlr]
        _ = r * r * l := by rw [mul_assoc]
    have hlC : l ∈ C := by
      rw [hC]
      exact ⟨hlX, mem_centralizer_singleton_iff.2 hlt⟩
    rcases h.cent_E ⟨l, hlC⟩
      (fun s hs => Subtype.ext (hl s (hCX s.2) (congrArg Subtype.val hs))) with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)
  · obtain ⟨⟨β, hβC⟩, hβt, hβ3, hcard, d₁, hd₁, d₂, hd₂, hne⟩ := h.beta
    have himg : (rootGroup ↥C ⟨t, htC⟩ ⊓ centralizer ({(⟨β, hβC⟩ : ↥C)} : Set ↥C)).map
        C.subtype = closure (rootSet X t) ⊓ centralizer ({β} : Set G) := by
      rw [Subgroup.map_inf _ _ _ C.subtype_injective, map_rootGroup htC,
        map_centralizer_subtype hβC, ← inf_assoc, inf_of_le_left (closure_rootSet_le C t), hR]
    refine ⟨β, hCX hβC, congrArg Subtype.val hβt,
      (Subgroup.orderOf_coe (⟨β, hβC⟩ : ↥C)).trans hβ3, ?_, d₁, ?_, d₂, ?_, ?_⟩
    · rw [← himg, Subgroup.card_map_of_injective C.subtype_injective]
      exact hcard
    · rw [← himg]
      exact ⟨d₁, hd₁, rfl⟩
    · rw [← himg]
      exact ⟨d₂, hd₂, rfl⟩
    · intro hc
      exact hne (Subtype.ext hc)

end Roots

section Restrict

variable {n k N : ℕ} {gs : ℕ → Perm (Fin n)} {rs : ℕ → Perm (Fin k)} {Ω : Fin k → Fin n}
  {X : Subgroup (Perm (Fin n))} {t : Perm (Fin n)} {tO : Perm (Fin k)}

theorem mem_of_closure_eq (htX : t ∈ X)
    (hcg : closure (gs '' {l | l < N}) = X ⊓ centralizer ({t} : Set (Perm (Fin n)))) :
    t ∈ closure (gs '' {l | l < N}) := by
  rw [hcg]
  exact ⟨htX, mem_centralizer_singleton_iff.2 rfl⟩

theorem restrictHom_t (hΩ : Function.Injective Ω) (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (htC : t ∈ closure (gs '' {l | l < N})) (htO : ∀ j, t (Ω j) = Ω (tO j)) :
    restrictHom hΩ hc ⟨t, htC⟩ = tO :=
  restrHom_eq hΩ htO

theorem tO_mem (hΩ : Function.Injective Ω) (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N})))
    (htC : t ∈ closure (gs '' {l | l < N})) (htO : ∀ j, t (Ω j) = Ω (tO j)) :
    tO ∈ closure (rs '' {l | l < N}) := by
  rw [← restrictHom_range hΩ hc hcard, ← restrictHom_t hΩ hc htC htO]
  exact ⟨_, rfl⟩

theorem closure_eq_inf_centralizer (htX : t ∈ X) (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcg : closure (gs '' {l | l < N}) = X ⊓ centralizer ({t} : Set (Perm (Fin n))))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N})))
    (htO : ∀ j, t (Ω j) = Ω (tO j)) :
    closure (rs '' {l | l < N}) =
      closure (rs '' {l | l < N}) ⊓ centralizer ({tO} : Set (Perm (Fin k))) := by
  have htC := mem_of_closure_eq htX hcg
  refine (inf_of_le_left fun y hy => ?_).symm
  rw [← restrictHom_range hΩ hc hcard] at hy
  obtain ⟨c, rfl⟩ := hy
  have hcC : (c : Perm (Fin n)) ∈ X ⊓ centralizer ({t} : Set (Perm (Fin n))) := by
    rw [← hcg]
    exact c.2
  have hct : (c : Perm (Fin n)) * t = t * c := mem_centralizer_singleton_iff.1 hcC.2
  have hct' : c * ⟨t, htC⟩ = ⟨t, htC⟩ * c := Subtype.ext hct
  rw [mem_centralizer_singleton_iff, ← restrictHom_t hΩ hc htC htO, ← map_mul, ← map_mul, hct']

theorem eLabelling_of_restrict (htX : t ∈ X) (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcg : closure (gs '' {l | l < N}) = X ⊓ centralizer ({t} : Set (Perm (Fin n))))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N})))
    (htO : ∀ j, t (Ω j) = Ω (tO j)) {M : ℕ → ℕ → ℕ} {tI : ℕ}
    (hY : ∀ hO : tO ∈ closure (rs '' {l | l < N}), ∃ elt : ℕ → ↥(closure (rs '' {l | l < N})),
      ELabelling (rootGroup _ ⟨tO, hO⟩) ⟨tO, hO⟩ M tI elt) :
    ∃ elt : ℕ → ↥X, ELabelling (rootGroup ↥X ⟨t, htX⟩) ⟨t, htX⟩ M tI elt := by
  have htC := mem_of_closure_eq htX hcg
  have hO := tO_mem hΩ hc hcard htC htO
  obtain ⟨elt, hL⟩ := hY hO
  set e := (restrictEquiv hΩ hc hcard).symm
  have he : e ⟨tO, hO⟩ = ⟨t, htC⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (restrictHom_t hΩ hc htC htO).symm
  have h1 := hL.transport e
  rw [he] at h1
  have hCX : closure (gs '' {l | l < N}) ≤ X := by
    rw [hcg]
    exact inf_le_left
  have hroot : ∀ x ∈ X, x * x = t → x ∈ closure (gs '' {l | l < N}) := by
    intro x hx hxx
    rw [hcg]
    exact ⟨hx, mem_centralizer_singleton_iff.2 (by rw [← hxx, mul_assoc])⟩
  exact ⟨_, eLabelling_of_inclusion hCX htC hroot h1⟩

theorem rootFactsFor_of_restrict (htX : t ∈ X) (hΩ : Function.Injective Ω)
    (hc : ∀ l < N, ∀ j, gs l (Ω j) = Ω (rs l j))
    (hcg : closure (gs '' {l | l < N}) = X ⊓ centralizer ({t} : Set (Perm (Fin n))))
    (hcard : Nat.card (closure (gs '' {l | l < N})) = Nat.card (closure (rs '' {l | l < N})))
    (htO : ∀ j, t (Ω j) = Ω (tO j))
    (hY : ∀ hO : tO ∈ closure (rs '' {l | l < N}),
      RootFactsFor ↥(closure (rs '' {l | l < N})) ⟨tO, hO⟩) :
    RootFactsFor ↥X ⟨t, htX⟩ := by
  have htC := mem_of_closure_eq htX hcg
  have hO := tO_mem hΩ hc hcard htC htO
  set e := (restrictEquiv hΩ hc hcard).symm
  have he : e ⟨tO, hO⟩ = ⟨t, htC⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (restrictHom_t hΩ hc htC htO).symm
  have h1 := (hY hO).of_mulEquiv e
  rw [he] at h1
  exact rootFactsFor_of_cent hcg htC htX h1

end Restrict

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem eLabelling_of_enums {n m capW : ℕ} (hn : n < 2 ^ 32)
    {X : Subgroup (Equiv.Perm (Fin n))} {tT : Table} {cg : Array Table}
    (htX : tp n tT ∈ X)
    (hcg : closure (tp n '' {x | x ∈ cg}) =
      X ⊓ centralizer ({tp n tT} : Set (Equiv.Perm (Fin n))))
    (hperm : permOK n tT = true)
    (hWchk : enumOK n m cg (mulClosureS n m cg capW) 1920 = true)
    (hEchk : enumOK n m (wRoots n tT (mulClosureS n m cg capW).1)
      (mulClosureS n m (wRoots n tT (mulClosureS n m cg capW).1) 40) 32 = true)
    (hclosed : tblClosedOK n (mulClosureS n m (wRoots n tT (mulClosureS n m cg capW).1) 40).1 =
      true)
    (htIlt : wUIdx n m capW tT cg <
      (mulClosureS n m (wRoots n tT (mulClosureS n m cg capW).1) 40).1.size)
    (htIeq : tblEq n (mulClosureS n m (wRoots n tT (mulClosureS n m cg capW).1) 40).1[
      wUIdx n m capW tT cg]! tT = true) :
    ∃ elt : ℕ → ↥X, ELabelling (rootGroup ↥X ⟨tp n tT, htX⟩) (⟨tp n tT, htX⟩ : ↥X)
      (wUMul n m capW tT cg) (wUIdx n m capW tT cg) elt := by
  classical
  obtain ⟨hWs, -⟩ := enumOK_spec hn hWchk
  obtain ⟨hEs, hEsize⟩ := enumOK_spec hn hEchk
  set W := (mulClosureS n m cg capW).1 with hWdef
  set rts := wRoots n tT W with hrtsdef
  set El := (mulClosureS n m rts 40).1 with hEldef
  have hRs : rootSet X (tp n tT) = tp n '' {x | x ∈ rts} :=
    rootSet_eq_image_wRoots hperm hWs hEs.perm hcg
  set K := closure (tp n '' {x | x ∈ rts}) with hK
  have hmap : (rootGroup ↥X ⟨tp n tT, htX⟩).map X.subtype = K := by
    rw [map_rootGroup htX, hRs]
  have hKX : K ≤ X := by
    rw [hK, ← hRs]
    exact closure_rootSet_le X (tp n tT)
  have hmemX : ∀ k (h : k < El.size), tablePerm n El[k]! ∈ X := fun k h => hKX (hEs.mem k h)
  let elt : ℕ → ↥X := fun k => if h : k < El.size then ⟨tablePerm n El[k]!, hmemX k h⟩ else 1
  have helt : ∀ k (h : k < El.size), (elt k : Equiv.Perm (Fin n)) = tablePerm n El[k]! := by
    intro k h
    simp [elt, h]
  refine ⟨elt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha' : a < El.size := by omega
    have h1 : (elt a : Equiv.Perm (Fin n)) ∈ K := by
      rw [helt a ha']
      exact hEs.mem a ha'
    rw [← hmap] at h1
    exact (Subgroup.mem_map_iff_mem X.subtype_injective).1 h1
  · intro e he
    have h1 : (e : Equiv.Perm (Fin n)) ∈ K := by
      rw [← hmap]
      exact ⟨e, he, rfl⟩
    obtain ⟨k, hk, hrep⟩ := hEs.cover _ h1
    refine ⟨k, by omega, Subtype.ext ?_⟩
    rw [helt k hk]
    exact tablePerm_eq hrep
  · intro a ha b hb hab
    have ha' : a < El.size := by omega
    have hb' : b < El.size := by omega
    have h1 := congrArg Subtype.val hab
    rw [helt a ha', helt b hb'] at h1
    exact hEs.inj ha' hb' h1
  · intro a ha b hb
    have := (tblClosedOK_spec hclosed (a := a) (b := b) (by omega) (by omega)).1
    change tblMulIdx n El a b < 32
    omega
  · intro a ha b hb
    have ha' : a < El.size := by omega
    have hb' : b < El.size := by omega
    obtain ⟨hc, hceq⟩ := tblClosedOK_spec hclosed ha' hb'
    apply Subtype.ext
    change (elt (tblMulIdx n El a b) : Equiv.Perm (Fin n)) = (elt a * elt b : ↥X)
    rw [helt _ hc, Subgroup.coe_mul, helt _ ha', helt _ hb']
    exact ((tblEq_iff_eq (Rep.compT (hEs.rep a ha') (hEs.rep b hb')) (hEs.rep _ hc)).1 hceq).symm
  · obtain ⟨hpos, h0⟩ := tablePerm_zero_of_enumOK hn hEchk
    apply Subtype.ext
    rw [helt 0 hpos, Subgroup.coe_one]
    exact h0
  · change El.findIdx (fun T => tblEq n T tT) < 32
    have : El.findIdx (fun T => tblEq n T tT) < El.size := htIlt
    omega
  · apply Subtype.ext
    change (elt (El.findIdx (fun T => tblEq n T tT)) : Equiv.Perm (Fin n)) = tp n tT
    have htIlt' : El.findIdx (fun T => tblEq n T tT) < El.size := htIlt
    rw [helt _ htIlt']
    exact (tblEq_iff_eq (hEs.rep _ htIlt) (rep_tp hperm)).1 htIeq

open CFSG.KC.YoshQ

section Recs

variable {n w : Nat} {gens : Array Table} {t : Nat} {GS RW : List Nat} {cW EPW PLW POSW : Nat}
  {SMW SFW GE RE : List Nat} {cE EPE PLE POSE : Nat} {SME SFE : List Nat}

theorem OmRecs.eLabelling (h : OmRecs n w gens t GS RW cW EPW PLW POSW SMW SFW GE RE cE EPE PLE
    POSE SME SFE) {X : Subgroup (Equiv.Perm (Fin n))} (htX : tp n (tabN n w t) ∈ X)
    (hcg : closure (tp n '' {x | x ∈ gens}) =
      X ⊓ centralizer ({tp n (tabN n w t)} : Set (Equiv.Perm (Fin n))))
    (hcl : closedN n w RE = true) {M : Nat → Nat → Nat}
    (hM : ∀ a < 32, ∀ b < 32, mulIdxN n w RE a b = M a b) {tI : Nat}
    (htI : RE.findIdx (fun x => eqN n w x t) = tI) (htI32 : tI < 32)
    (htIe : eqN n w (RE.getD tI 0) t = true) :
    ∃ elt : ℕ → ↥X, ELabelling (rootGroup ↥X ⟨tp n (tabN n w t), htX⟩)
      (⟨tp n (tabN n w t), htX⟩ : ↥X) M tI elt := by
  have hl := h.lenE
  have hE1 : (mulClosureS n n (wRoots n (tabN n w t) (mulClosureS n n gens 2000).1) 40).1 =
      (RE.map (tabN n w)).toArray := by
    rw [h.roots_eq, h.closureE]
  have hfi : wUIdx n n 2000 (tabN n w t) gens = tI := by
    unfold wUIdx wUTabs
    rw [hE1, List.findIdx_toArray, List.findIdx_map, ← htI]
    congr 1
    funext x
    simp only [Function.comp, tblEq_tabN' h.dims]
  have hEchk := h.enumE
  rw [← h.roots_eq] at hEchk
  have hcl' : tblClosedOK n
      (mulClosureS n n (wRoots n (tabN n w t) (mulClosureS n n gens 2000).1) 40).1 = true := by
    rw [hE1, tblClosedOK_tabN h.dims]
    exact hcl
  have hlt : wUIdx n n 2000 (tabN n w t) gens <
      (mulClosureS n n (wRoots n (tabN n w t) (mulClosureS n n gens 2000).1) 40).1.size := by
    rw [hfi, hE1]
    simpa [hl] using htI32
  have heq : tblEq n (mulClosureS n n (wRoots n (tabN n w t) (mulClosureS n n gens 2000).1)
      40).1[wUIdx n n 2000 (tabN n w t) gens]! (tabN n w t) = true := by
    rw [hfi, hE1, toArray_map_tabN_getElem! RE (by omega), tblEq_tabN' h.dims]
    exact htIe
  obtain ⟨elt, hL⟩ := eLabelling_of_enums h.dims.n_lt32 htX hcg h.permT h.enumW hEchk hcl' hlt heq
  refine ⟨elt, ?_⟩
  rw [hfi] at hL
  refine eLabelling_congr hL fun a ha b hb => ?_
  unfold wUMul wUTabs
  rw [hE1, tblMulIdx_tabN h.dims RE (by omega) (by omega)]
  exact hM a ha b hb

end Recs

section Tables

open CFSG.KC.Enum CFSG.KS

variable {n : Nat}

theorem tp_val {T : Table} (h : permOK n T = true) (i : Fin n) : ((tp n T i : Fin n) : ℕ) = ap T i := by
  have h1 := rep_tp h i i.2
  rw [idx_of_lt _ i.2] at h1
  exact h1.symm

theorem tp_unpack {w F : Nat} {T : Table} (h : permOK n T = true)
    (hT : natArr T = CFSG.KS.Raw.unpack n w F) (i : Fin n) :
    ((tp n T i : Fin n) : ℕ) = pg w (mask w) F i := by
  rw [tp_val h, ← natArr_getElem!, hT, CFSG.KS.Raw.unpack,
    getElem!_pos _ (i : ℕ) (by simp), Array.getElem_ofFn]

theorem tp_tabN {w x : Nat} (hw : w ≤ 32) (h : permOK n (tabN n w x) = true) (j : Fin n) :
    ((tp n (tabN n w x) j : Fin n) : ℕ) = pg w (mask w) x j := by
  rw [tp_val h, ap_tabN hw, pg_mod j.2]

end Tables

end CFSG.KC.Fin76bOm

end
