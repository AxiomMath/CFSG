module

public import CFSG.ClassicalInvolution.Q3.TL3T11

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure AETwinRel (Ω : Set (Subgroup G)) (A : Subgroup G)
    (tw : Subgroup G → Subgroup G → Prop) : Prop where
  pair : ∀ {L L' : Subgroup G}, tw L L' → MaxAdj (nbrAdj Ω) A L ∧ MaxAdj (nbrAdj Ω) A L' ∧
    L ≠ L' ∧ ∀ u u' : G, IsUniqueInvolution L u → IsUniqueInvolution L' u' →
      CentX Ω A (u * u')
  partner : ∀ {L : Subgroup G}, MaxAdj (nbrAdj Ω) A L → ∃ L' : Subgroup G, tw L L'
  sameNbr : ∀ {L L' : Subgroup G}, tw L L' → ∀ L'' : Subgroup G, MaxAdj (nbrAdj Ω) A L'' →
    L'' ≠ L → L'' ≠ L' → (∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) → ∀ x ∈ L', ∀ w ∈ L'', x * w = w * x
  cong : ∀ {L L' : Subgroup G} {a : G}, tw L L' → IsUniqueInvolution A a →
    ∀ l ∈ L, ∃ l' ∈ L', l⁻¹ * l' ∈ Qz a
  yElt : ∀ {L L' : Subgroup G} {u : G}, tw L L' → IsUniqueInvolution L u →
    ∃ y ∈ pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧
      y * u = u * y ∧ y ∈ Subgroup.normalizer (L' : Set G) ∧ (∃ l' ∈ L', y * l' ≠ l' * y) ∧
      ∀ L'' : Subgroup G, MaxAdj (nbrAdj Ω) A L'' → L'' ≠ L → L'' ≠ L' →
        (∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) → ∀ w ∈ L'', y * w = w * y

variable {Ω : Set (Subgroup G)} {K : Subgroup G} (hS : ThinStd Ω K)
include hS

theorem ThinStd.false_of_triangle_of_aeTwinRel
    (hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    {M N N' : Subgroup G} {twM twN : Subgroup G → Subgroup G → Prop}
    (hTM : AETwinRel Ω M twM) (hTN : AETwinRel Ω N twN) (htw : twM N N')
    {u u' : G} (hu : IsUniqueInvolution N u) (hu' : IsUniqueInvolution N' u')
    (hNN' : MaxAdj (nbrAdj Ω) N N') : False := by
  obtain ⟨hN, hN', hne, -⟩ := hTM.pair htw
  obtain ⟨y, hyX, ⟨k, hy3⟩, hyu, hyN', ⟨l₀, hl₀, hl₀y⟩, hycent⟩ := hTM.yElt htw hu
  obtain ⟨N'', htw''⟩ := hTN.partner hNN'
  obtain ⟨-, hN'', hne'', -⟩ := hTN.pair htw''
  have hNM : MaxAdj (nbrAdj Ω) N M := hS.maxAdj_symm hN
  have hMN' : M ≠ N' := fun h => hN'.1.2.2.1 h.symm
  have hyN'' : ∀ w ∈ N'', y * w = w * y := by
    have hNN''c : ∀ x ∈ N, ∀ w ∈ N'', x * w = w * x := hS.commutes_of_nbrAdj hN''.1
    by_cases hM'' : N'' = M
    · intro w hw
      rw [hM''] at hw
      refine (comm_of_mem_pSpan hyX fun J hJ j hj => ?_).symm
      exact (hS.commutes_of_nbrAdj (show MaxAdj (nbrAdj Ω) M J from hJ).1 w hw j hj)
    · by_cases hmax : MaxAdj (nbrAdj Ω) M N''
      · refine hycent N'' hmax (fun h => ?_) (Ne.symm hne'') hNN''c
        exact hN''.1.2.2.1 h
      · have hMc : ∀ x ∈ M, ∀ w ∈ N'', x * w = w * x := by
          have := hTN.sameNbr htw'' M hNM hMN' (fun h => hM'' h.symm)
            (fun x hx w hw => (hS.commutes_of_nbrAdj hN'.1 w hw x hx).symm)
          exact fun x hx w hw => (this w hw x hx).symm
        have hadj : nbrAdj Ω M N'' := by
          refine ⟨hN.1.1, (mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hN''.1.2.1, hM'', ?_⟩⟩
          intro w hw
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            have h1 : w * x * w⁻¹ = x := by rw [← hMc x hx w hw]; group
            rw [h1]
            exact hx
          · intro hx
            have h1 : w * x * w⁻¹ = x := by
              have h2 := hMc (w * x * w⁻¹) hx w hw
              calc w * x * w⁻¹ = w⁻¹ * (w * (w * x * w⁻¹)) := by group
                _ = w⁻¹ * ((w * x * w⁻¹) * w) := by rw [h2]
                _ = x := by group
            rw [← h1]
            exact hx
        intro w hw
        refine (comm_of_mem_pSpan hyX fun J hJ j hj => ?_).symm
        have hJ' : MaxAdj (nbrAdj Ω) M J := hJ
        have hnot : N'' ∉ orbOf (nbrAdj Ω) M J := fun h => hmax ((hS.maxAdj_iff_mem_orbOf hJ').mpr h)
        exact (hS.commutes_of_nbrAdj (hS.sep hJ'.1 hadj hnot) j hj w hw).symm
  have hyC : y ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyu
  have hcong := hTN.cong htw'' hu
  have hact : ∀ l ∈ N', y * l * y⁻¹ = l ∨ y * l * y⁻¹ = l * u' := by
    intro l hl
    obtain ⟨l'', hl'', hq⟩ := hcong l hl
    set q := l⁻¹ * l'' with hqdef
    have hyq : y * q * y⁻¹ ∈ Qz u := (isNormalTwoIn_Qz u).2.2 y hyC q hq
    have hlq : l = l'' * q⁻¹ := by rw [hqdef]; group
    have hyl'' : y * l'' * y⁻¹ = l'' := by rw [hyN'' l'' hl'']; group
    have hx : l⁻¹ * (y * l * y⁻¹) = q * (y * q * y⁻¹)⁻¹ := by
      calc l⁻¹ * (y * l * y⁻¹) = l⁻¹ * ((y * l'' * y⁻¹) * (y * q * y⁻¹)⁻¹) := by
            rw [hlq]; group
        _ = l⁻¹ * (l'' * (y * q * y⁻¹)⁻¹) := by rw [hyl'']
        _ = q * (y * q * y⁻¹)⁻¹ := by rw [hqdef]; group
    have hxQ : l⁻¹ * (y * l * y⁻¹) ∈ Qz u := by
      rw [hx]
      exact (Qz u).mul_mem hq ((Qz u).inv_mem hyq)
    have hxN : l⁻¹ * (y * l * y⁻¹) ∈ N' :=
      N'.mul_mem (N'.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hyN' l).mp hl)
    rcases hS.eq_of_mem_Qz hNN'.1 (hall N N' hNN') hu hu' hxN hxQ with h1 | h1
    · left
      calc y * l * y⁻¹ = l * (l⁻¹ * (y * l * y⁻¹)) := by group
        _ = l := by rw [h1, mul_one]
    · right
      calc y * l * y⁻¹ = l * (l⁻¹ * (y * l * y⁻¹)) := by group
        _ = l * u' := by rw [h1]
  exact hl₀y (comm_of_conj_mem_mul hu' hy3 hyN' hact l₀ hl₀)

theorem ThinStd.false_of_aeTwinRel (hZ : Subgroup.center G = ⊥)
    (hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    {M N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N) {twM : Subgroup G → Subgroup G → Prop}
    (hTM : AETwinRel Ω M twM)
    (hTN : ∀ L : Subgroup G, MaxAdj (nbrAdj Ω) M L → ∃ tw : Subgroup G → Subgroup G → Prop,
      AETwinRel Ω L tw) : False := by
  obtain ⟨N', htw⟩ := hTM.partner hN
  obtain ⟨-, hN', hne, hc⟩ := hTM.pair htw
  obtain ⟨u, hu⟩ := (hS.hyp.omega1 N hN.1.2.1).1
  obtain ⟨u', hu'⟩ := (hS.hyp.omega1 N' hN'.1.2.1).1
  have hNN' := hS.maxAdj_of_centX_mul hZ hN hN' hne hu hu' (hc u u' hu hu')
  obtain ⟨twN, hTN'⟩ := hTN N hN
  exact hS.false_of_triangle_of_aeTwinRel hall hTM hTN' htw hu hu' hNN'

@[expose] def AEIdent.twinRel {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n)
    (L L' : Subgroup G) : Prop :=
  L ∈ P ∧ L' ∈ P ∧ ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
    (L.subgroupOf (pSpan P)).map I.φ = AE.memBar α h b ∧
      (L'.subgroupOf (pSpan P)).map I.φ = AE.memBar α h (!b)

theorem ThinStd.disjoint_of_comm_of_twinRel {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n) (hk : IsPGroup 2 I.φ.ker)
    {L L' : Subgroup G} (hL : MaxAdj (nbrAdj Ω) A L) (hL' : MaxAdj (nbrAdj Ω) A L')
    {u : G} (hu : IsUniqueInvolution L u) {α : Finset (Fin n)} {h : α.card = 4} {b : Bool}
    (hlab : (L.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar α h (!b))
    {L'' : Subgroup G} (hL'' : MaxAdj (nbrAdj Ω) A L'') (hne1 : L'' ≠ L) (hne2 : L'' ≠ L')
    (hcomm : ∀ x ∈ L, ∀ w ∈ L'', x * w = w * x) {β : Finset (Fin n)} {h'' : β.card = 4}
    {c : Bool}
    (hlab'' : (L''.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ =
      AE.memBar β h'' c) :
    Disjoint α β := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  have hβ : α ≠ β := by
    rintro rfl
    by_cases hcb : c = b
    · subst hcb
      exact hne1 (hS.eq_of_map_le hPΩ hn I hk hL'' hL (le_of_eq (hlab''.trans hlab.symm)))
    · have hcb' : c = !b := by cases b <;> cases c <;> simp_all
      subst hcb'
      exact hne2 (hS.eq_of_map_le hPΩ hn I hk hL'' hL' (le_of_eq (hlab''.trans hlab'.symm)))
  have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
  refine AE.disjoint_of_zBar_comm (h := h) (h' := h'') hβ (c := c) fun y hy => ?_
  rw [← hlab''] at hy
  obtain ⟨w, hw, rfl⟩ := I.exists_of_mem_map hL'' hy
  rw [← hz, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcomm u hu.mem w hw)

theorem ThinStd.aeTwinRel_of_aeIdent {A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} n)
    (hO : classicalInvolutionOddCore ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}) = ⊥) :
    AETwinRel Ω A I.twinRel := by
  have hPΩ : {M : Subgroup G | MaxAdj (nbrAdj Ω) A M} ⊆ Ω := fun M hM => hM.1.2.1
  have hk := I.isPGroup_ker hO
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro L L' ⟨hL, hL', α, h, b, hlab, hlab'⟩
    refine ⟨hL, hL', fun heq => ?_, fun u u' hu hu' => ?_⟩
    · subst heq
      rw [hlab] at hlab'
      cases b
      · exact AE.memBar_true_ne_false hn α h hlab'.symm
      · exact AE.memBar_true_ne_false hn α h hlab'
    · have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
      have hz' := I.map_eq_zBar hn hL' (hS.card L' (hPΩ hL')) hlab' hu'
      have hker : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u', le_pSpan hL' hu'.mem⟩ : ↥(pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})) ∈
          I.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, hz, hz']
        exact AE.zBar_mul_self α h
      intro M hM m hm
      have := Subgroup.mem_center_iff.mp (I.ker_le hker) ⟨m, le_pSpan hM hm⟩
      exact (congrArg Subtype.val this).symm
  ·
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    obtain ⟨L', hL', hlab'⟩ := I.label_surj α h (!b)
    exact ⟨L', hL, hL', α, h, b, hlab, hlab'⟩
  ·
    rintro L L' ⟨hL, hL', α, h, b, hlab, hlab'⟩ L'' hL'' hne1 hne2 hcomm
    obtain ⟨u, hu⟩ := (hS.hyp.omega1 L (hPΩ hL)).1
    obtain ⟨β, h'', c, hlab''⟩ := I.label L'' hL''
    have hd := hS.disjoint_of_comm_of_twinRel hn I hk hL hL' hu hlab hlab' hL'' hne1 hne2 hcomm
      hlab''
    refine hS.commutes_of_map_comm hPΩ I hk hL' hL'' (Ne.symm hne2) ?_
    rw [hlab', hlab'']
    exact AE.comm_memBar_of_disjoint hd (!b) c
  ·
    rintro L L' a ⟨hL, hL', α, h, b, hlab, hlab'⟩ ha l hl
    have hmem := I.mem_map hL hl
    rw [hlab] at hmem
    obtain ⟨m, hm, hme⟩ := hmem
    obtain ⟨m', hm', hmm'⟩ := AE.memAt_mul_vec α h b m hm
    have hm'mem : AE.mkQ n m' ∈ (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ := by
      rw [hlab']
      exact ⟨m', hm', rfl⟩
    obtain ⟨l', hl', hl'e⟩ := I.exists_of_mem_map hL' hm'mem
    refine ⟨l', hl', ?_⟩
    have hVn : ((AE.vecSub n).map (AE.mkQ n)).Normal :=
      AE.vecSub_normal.map _ (QuotientGroup.mk'_surjective _)
    have hlF : l⁻¹ * l' ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype := by
      refine ⟨⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩, ?_, rfl⟩
      show I.φ (⟨l, le_pSpan hL hl⟩⁻¹ * ⟨l', le_pSpan hL' hl'⟩) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_inv, hl'e, ← hme, ← map_inv, ← map_mul]
      exact ⟨_, hmm', rfl⟩
    have hFn : ∀ x ∈ pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}, ∀ q ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map
        (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype, x * q * x⁻¹ ∈ (((AE.vecSub n).map (AE.mkQ n)).comap I.φ).map
          (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M}).subtype := by
      intro x hx q hq
      obtain ⟨q', hq', rfl⟩ := hq
      refine ⟨⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹, ?_, rfl⟩
      show I.φ (⟨x, hx⟩ * q' * ⟨x, hx⟩⁻¹) ∈ (AE.vecSub n).map (AE.mkQ n)
      rw [map_mul, map_mul, map_inv]
      exact hVn.conj_mem _ hq' _
    have hV2 : IsPGroup 2 ((AE.vecSub n).map (AE.mkQ n)) := by
      rintro ⟨_, v, hv, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, pow_one, pow_two, ← map_mul, AE.vecSub_mul_self hv, map_one]
      rfl
    exact hS.le_Qz_of_normal ha (Subgroup.map_subtype_le _) hFn
      ((hV2.comap_of_ker_isPGroup I.φ hk).map _) hlF
  ·
    rintro L L' u ⟨hL, hL', α, h, b, hlab, hlab'⟩ hu
    obtain ⟨a, ha⟩ := (hS.hyp.omega1 A hL.1.1).1
    have hrange : AE.yBar α h ∈ I.φ.range := by
      rw [I.range_eq]
      exact AE.yBar_mem α h
    obtain ⟨y, hy, k, hyk⟩ := I.exists_lift_pow_three hrange (AE.yBar_pow_three α h)
    have hz := I.map_eq_zBar hn hL (hS.card L (hPΩ hL)) hlab hu
    refine ⟨(y : G), y.2, ⟨k, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val hyk
      rwa [Subgroup.coe_pow] at this
    · have := I.comm_of_pow_three hk hyk (w := ⟨u, le_pSpan hL hu.mem⟩)
        (by rw [hy, hz]; exact AE.yBar_comm_zBar α h)
      exact congrArg Subtype.val this
    · have hL'y : MaxAdj (nbrAdj Ω) A (conjSub (y : G) L') :=
        hS.maxAdj_conj_of_mem hL' ha (hS.pSpan_le_centralizer ha y.2)
      have hle : ((conjSub (y : G) L').subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ ≤
          (L'.subgroupOf (pSpan {M : Subgroup G | MaxAdj (nbrAdj Ω) A M})).map I.φ := by
        intro x hx
        obtain ⟨x', hx', rfl⟩ := I.exists_of_mem_map hL'y hx
        have h1 : (y : G)⁻¹ * x' * y ∈ L' := mem_conjSub_iff.mp hx'
        have h2 : I.φ ⟨x', le_pSpan hL'y hx'⟩ =
            I.φ y * I.φ ⟨(y : G)⁻¹ * x' * y, le_pSpan hL' h1⟩ * (I.φ y)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          show x' = (y : G) * ((y : G)⁻¹ * x' * y) * (y : G)⁻¹
          group
        have h3 := I.mem_map hL' h1
        rw [hlab'] at h3 ⊢
        rw [h2, hy]
        exact AE.yBar_conj_mem_memBar α h (!b) _ h3
      exact mem_normalizer_of_conjSub_eq (hS.eq_of_map_le hPΩ hn I hk hL'y hL' hle)
    · obtain ⟨x, hx, hxy⟩ := AE.yBar_not_comm_memBar hn α h (!b)
      rw [← hlab'] at hx
      obtain ⟨l', hl', rfl⟩ := I.exists_of_mem_map hL' hx
      refine ⟨l', hl', fun he => hxy ?_⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext he
    · intro L'' hL'' hne1 hne2 hcomm w hw
      obtain ⟨β, h'', c, hlab''⟩ := I.label L'' hL''
      have hd := hS.disjoint_of_comm_of_twinRel hn I hk hL hL' hu hlab hlab' hL'' hne1 hne2
        hcomm hlab''
      have h3 := I.mem_map hL'' hw
      rw [hlab''] at h3
      have := I.comm_of_pow_three hk hyk (w := ⟨w, le_pSpan hL'' hw⟩)
        (by rw [hy]; exact AE.yBar_comm_memBar_of_disjoint hd c _ h3)
      exact congrArg Subtype.val this

theorem ThinStd.false_of_aeIdent (hZ : Subgroup.center G = ⊥)
    (hall : ∀ M N : Subgroup G, MaxAdj (nbrAdj Ω) M N → ThinAt Ω M N)
    {M N : Subgroup G} (hN : MaxAdj (nbrAdj Ω) M N) {n : ℕ} (hn : 5 ≤ n)
    (I : AEIdent {L : Subgroup G | MaxAdj (nbrAdj Ω) M L} n)
    (hO : classicalInvolutionOddCore ↥(pSpan {L : Subgroup G | MaxAdj (nbrAdj Ω) M L}) = ⊥)
    (hconj : ∀ L ∈ Ω, ∃ g : G, conjSub g M = L) : False := by
  refine hS.false_of_aeTwinRel hZ hall hN (hS.aeTwinRel_of_aeIdent hn I hO) fun L hL => ?_
  obtain ⟨g, rfl⟩ := hconj L hL.1.2.1
  exact ⟨_, hS.aeTwinRel_of_aeIdent hn (hS.aeIdent_conj I g) (hS.oddCore_pSpan_conj hO g)⟩

end CFSG.ClassicalInvolution.Q3.TC.Thin
