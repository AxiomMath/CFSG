module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142N

open CFSG.Open
open scoped commutatorElement

section Basic

variable {G : Type*} [Group G]

theorem comm_mul_central_left {x y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzy : y * z = z * y := Subgroup.mem_center_iff.1 hz y
  calc ⁅x * z, y⁆ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem comm_mul_central_right {x y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have hzx : z * x⁻¹ = x⁻¹ * z := (Subgroup.mem_center_iff.1 hz x⁻¹).symm
  calc ⁅x, y * z⁆ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

theorem commutatorElement_mem_of {N : Subgroup G} {n m : G} (hn : n ∈ N) (hm : m ∈ N) :
    ⁅n, m⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)

theorem map_subtype_top (K : Subgroup G) : Subgroup.map K.subtype ⊤ = K := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem comm_self_eq_of_commutator_top {K : Subgroup G} (h : commutator K = ⊤) :
    ⁅K, K⁆ = K := by
  have h1 : Subgroup.map K.subtype (commutator K) = Subgroup.map K.subtype ⊤ := by rw [h]
  have h2 : Subgroup.map K.subtype (commutator K) = ⁅K, K⁆ := by
    show Subgroup.map K.subtype ⁅(⊤ : Subgroup K), ⊤⁆ = _
    rw [Subgroup.map_commutator, map_subtype_top]
  rw [← h2, h1, map_subtype_top]

theorem commutator_top_of_comm_self_eq {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    commutator K = ⊤ := by
  apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
  rw [map_subtype_top]
  show Subgroup.map K.subtype ⁅(⊤ : Subgroup K), ⊤⁆ = K
  rw [Subgroup.map_commutator, map_subtype_top, h]

theorem center_ne_top_of_commutator_top {Q : Type*} [Group Q] [Nontrivial Q]
    (hcomm : commutator Q = ⊤) : Subgroup.center Q ≠ ⊤ := by
  intro htop
  have hbot : commutator Q = ⊥ := by
    rw [eq_bot_iff]
    show ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    have ha : a ∈ Subgroup.center Q := htop ▸ Subgroup.mem_top a
    have hab : a * b = b * a := (Subgroup.mem_center_iff.1 ha b).symm
    rw [Subgroup.mem_bot, commutatorElement_def, hab]
    group
  rw [hcomm] at hbot
  exact top_ne_bot hbot

theorem quasisimple_dichotomy {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    {N : Subgroup Q} [N.Normal] : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hcomm, hsimp⟩ := hQ
  haveI : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    intro x hx
    have hmem : QuotientGroup.mk x ∈ N.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).1 hmem
  · left
    have hle : commutator Q ≤ N := by
      show ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ N
      rw [Subgroup.commutator_le]
      intro a _ b _
      have ha : QuotientGroup.mk a ∈ N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]; exact Subgroup.mem_top _
      have hb : QuotientGroup.mk b ∈ N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.1 ha
      obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.1 hb
      have hna' := QuotientGroup.eq.1 hna
      have hmb' := QuotientGroup.eq.1 hmb
      obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Subgroup.center Q, a = n * c :=
        ⟨n⁻¹ * a, hna', by group⟩
      obtain ⟨d, hd, rfl⟩ : ∃ d ∈ Subgroup.center Q, b = m * d :=
        ⟨m⁻¹ * b, hmb', by group⟩
      rw [comm_mul_central_left hc, comm_mul_central_right hd]
      exact commutatorElement_mem_of hn hm
    rw [hcomm] at hle
    exact eq_top_iff.2 hle

theorem isSimpleGroup_mod_center {Q : Type*} [Group Q]
    (hnt : Nontrivial (Q ⧸ Subgroup.center Q))
    (hdich : ∀ N : Subgroup Q, N.Normal → N = ⊤ ∨ N ≤ Subgroup.center Q) :
    IsSimpleGroup (Q ⧸ Subgroup.center Q) := by
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun M hM => ?_ }
  haveI := hM
  haveI : (M.comap (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.comap hM _
  rcases hdich (M.comap (QuotientGroup.mk' (Subgroup.center Q))) inferInstance with h | h
  · right
    apply eq_top_iff.2
    intro x _
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y ∈ M.comap (QuotientGroup.mk' (Subgroup.center Q)) := by
      rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_comap.1 hy
  · left
    apply eq_bot_iff.2
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : y ∈ M.comap (QuotientGroup.mk' (Subgroup.center Q)) := by
      rw [Subgroup.mem_comap]; exact hx
    have hy' : y ∈ Subgroup.center Q := h hy
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff y).2 hy'

end Basic

section Lift

variable {G H : Type*} [Group G] [Group H]

theorem comm_central_mul_left {x y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅z * x, y⁆ = ⁅x, y⁆ := by
  rw [← Subgroup.mem_center_iff.1 hz x]
  exact comm_mul_central_left hz

theorem comm_central_mul_right {x y z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z * y⁆ = ⁅x, y⁆ := by
  rw [← Subgroup.mem_center_iff.1 hz y]
  exact comm_mul_central_right hz

theorem commutator_normal_subgroupOf (M : Subgroup G) : (⁅M, M⁆.subgroupOf M).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hle : ⁅M, M⁆ ≤ ⁅M, M⁆.comap (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    have h1 : (g : G) * a * (g : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 ha) (M.inv_mem g.2)
    have h2 : (g : G) * b * (g : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 hb) (M.inv_mem g.2)
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    have h4 : (MulAut.conj (g : G)).toMonoidHom ⁅a, b⁆ = ⁅(g : G) * a * (g : G)⁻¹, (g : G) * b * (g : G)⁻¹⁆ := by
      show (g : G) * ⁅a, b⁆ * (g : G)⁻¹ = _
      simp only [commutatorElement_def]
      group
    rw [h4]
    exact h3
  have := hle hn
  rw [Subgroup.mem_comap] at this
  simpa [MulAut.conj_apply] using this

theorem map_commutator_eq_of {π : G →* H} {M : Subgroup G} {Kb : Subgroup H}
    (hM : M.map π = Kb) (hKb : IsQuasisimple Kb) : Subgroup.map π ⁅M, M⁆ = Kb := by
  have h1 : Subgroup.map π ⁅M, M⁆ = ⁅M.map π, M.map π⁆ := Subgroup.map_commutator M M π
  rw [h1, hM]
  exact comm_self_eq_of_commutator_top hKb.1

theorem isQuasisimple_of_commutator_map {π : G →* H}
    (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G) {M K : Subgroup G} {Kb : Subgroup H}
    (hK : K = ⁅M, M⁆) (hM : M.map π = Kb) (hKb : IsQuasisimple Kb) : IsQuasisimple K := by
  obtain ⟨hKbc, hKbs⟩ := hKb
  have hKbq : IsQuasisimple Kb := ⟨hKbc, hKbs⟩
  haveI : Nontrivial Kb := by
    haveI := hKbs.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Kb ⧸ Subgroup.center Kb)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hKmap : K.map π = Kb := by
    rw [hK]
    exact map_commutator_eq_of hM hKbq
  have hKx : ∀ x ∈ M, ∃ k ∈ K, π k = π x := by
    intro x hx
    have hx' : π x ∈ K.map π := by
      rw [hKmap, ← hM]; exact Subgroup.mem_map_of_mem π hx
    obtain ⟨k, hk', hkx⟩ := Subgroup.mem_map.1 hx'
    exact ⟨k, hk', hkx⟩
  have hKperf : ⁅K, K⁆ = K := by
    apply le_antisymm
    · exact Subgroup.commutator_le.2 (fun a ha b hb => commutatorElement_mem_of ha hb)
    · refine le_trans (le_of_eq hK) ?_
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k₁, hk₁, hk₁x⟩ := hKx x hx
      obtain ⟨k₂, hk₂, hk₂y⟩ := hKx y hy
      have hc₁ : k₁⁻¹ * x ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hk₁x]; simp)
      have hc₂ : k₂⁻¹ * y ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hk₂y]; simp)
      have e : ⁅x, y⁆ = ⁅k₁ * (k₁⁻¹ * x), k₂ * (k₂⁻¹ * y)⁆ := by
        simp only [mul_inv_cancel_left]
      rw [e, comm_mul_central_left hc₁, comm_mul_central_right hc₂]
      exact Subgroup.commutator_mem_commutator hk₁ hk₂
  have hKcomm : commutator K = ⊤ := commutator_top_of_comm_self_eq hKperf
  obtain ⟨pK, hpK⟩ : ∃ pK : K →* Kb,
      ∀ k : K, ((pK k : Kb) : H) = π (k : G) := by
    have hmem : ∀ k : K, π (k : G) ∈ Kb := fun k => by
      rw [← hKmap]; exact Subgroup.mem_map_of_mem π k.2
    exact ⟨{ toFun := fun k => ⟨π (k : G), hmem k⟩
             map_one' := Subtype.ext (by simp)
             map_mul' := fun a b => Subtype.ext (by simp) }, fun k => rfl⟩
  have hpK_surj : Function.Surjective pK := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ K.map π := by rw [hKmap]; exact hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy'
    exact ⟨⟨x, hx⟩, Subtype.ext (hpK ⟨x, hx⟩)⟩
  have hpK_ker : ∀ k : K, pK k = 1 → k ∈ Subgroup.center K := by
    intro k hk1
    have hπk : π (k : G) = 1 := by
      have h := hpK k
      rw [hk1] at h
      simpa using h.symm
    have hc := hk (k : G) hπk
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hc y)
  haveI hKnt : Nontrivial K := hpK_surj.nontrivial
  have hZne : Subgroup.center K ≠ ⊤ := center_ne_top_of_commutator_top hKcomm
  haveI hnt : Nontrivial (K ⧸ Subgroup.center K) := by
    obtain ⟨g, hg⟩ : ∃ g : K, g ∉ Subgroup.center K := by
      by_contra hcon
      push_neg at hcon
      exact hZne (eq_top_iff.2 fun g _ => hcon g)
    exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
  refine ⟨hKcomm, isSimpleGroup_mod_center hnt ?_⟩
  intro N hN
  haveI := hN
  haveI : (N.map pK).Normal := Subgroup.Normal.map inferInstance pK hpK_surj
  rcases quasisimple_dichotomy hKbq (N := N.map pK) with h | h
  · left
    have hle : commutator K ≤ N := by
      show ⁅(⊤ : Subgroup K), ⊤⁆ ≤ N
      rw [Subgroup.commutator_le]
      intro a _ b _
      have ha : pK a ∈ N.map pK := by rw [h]; exact Subgroup.mem_top _
      have hb : pK b ∈ N.map pK := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.1 ha
      obtain ⟨m, hm, hmb⟩ := Subgroup.mem_map.1 hb
      have hc : n⁻¹ * a ∈ Subgroup.center K :=
        hpK_ker _ (by rw [map_mul, map_inv, hna]; simp)
      have hd : m⁻¹ * b ∈ Subgroup.center K :=
        hpK_ker _ (by rw [map_mul, map_inv, hmb]; simp)
      obtain ⟨c, hc', rfl⟩ : ∃ c ∈ Subgroup.center K, a = n * c := ⟨n⁻¹ * a, hc, by group⟩
      obtain ⟨d, hd', rfl⟩ : ∃ d ∈ Subgroup.center K, b = m * d := ⟨m⁻¹ * b, hd, by group⟩
      rw [comm_mul_central_left hc', comm_mul_central_right hd']
      exact commutatorElement_mem_of hn hm
    rw [hKcomm] at hle
    exact eq_top_iff.2 hle
  · right
    intro n hn
    have hu : ∀ a : K, ⁅n, a⁆ ∈ Subgroup.center K := by
      intro a
      apply hpK_ker
      rw [map_commutatorElement]
      have hpn : pK n ∈ Subgroup.center Kb := h (Subgroup.mem_map_of_mem pK hn)
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hpn (pK a)).symm
    have hconj : ∀ a : K, n * a * n⁻¹ = ⁅n, a⁆ * a := by
      intro a
      rw [commutatorElement_def]
      group
    have hcomm' : ∀ a b : K, n * ⁅a, b⁆ = ⁅a, b⁆ * n := by
      intro a b
      have h1 : n * ⁅a, b⁆ * n⁻¹ = ⁅a, b⁆ := by
        calc n * ⁅a, b⁆ * n⁻¹ = ⁅n * a * n⁻¹, n * b * n⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅⁅n, a⁆ * a, ⁅n, b⁆ * b⁆ := by rw [hconj a, hconj b]
          _ = ⁅a, b⁆ := by
              rw [comm_central_mul_left (hu a), comm_central_mul_right (hu b)]
      calc n * ⁅a, b⁆ = (n * ⁅a, b⁆ * n⁻¹) * n := by group
        _ = ⁅a, b⁆ * n := by rw [h1]
    have htop : (⊤ : Subgroup K) ≤ Subgroup.centralizer {n} := by
      rw [← hKcomm]
      show ⁅(⊤ : Subgroup K), ⊤⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff.1 hm]
      exact hcomm' a b
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := htop (Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg n (Set.mem_singleton n)).symm

theorem exists_component_lift (π : G →* H) (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {X : Subgroup G} {Kb : Subgroup H} (hKb : IsComponentOf Kb (X.map π)) :
    ∃ K : Subgroup G, IsComponentOf K X ∧ K.map π = Kb := by
  obtain ⟨hKbX, hsub, hq⟩ := hKb
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = X ⊓ Kb.comap π := ⟨_, rfl⟩
  have hMsub : IsSubnormal M X := by
    have h := isSubnormal_inf_comap π hsub X
    have hXle : X ≤ (X.map π).comap π := fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem π hx)
    rw [inf_eq_left.2 hXle] at h
    rw [hMdef]
    exact h
  have hMmap : M.map π = Kb := by
    rw [hMdef]
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hm).2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hKbX hy)
      exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_comap.2 hy⟩, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = ⁅M, M⁆ := ⟨_, rfl⟩
  have hKM : K ≤ M := by
    rw [hK]
    exact Subgroup.commutator_le.2 (fun a ha b hb => commutatorElement_mem_of ha hb)
  have hnorm : (K.subgroupOf M).Normal := by
    rw [hK]
    exact commutator_normal_subgroupOf M
  refine ⟨K, ⟨hKM.trans (isSubnormal_le hMsub), IsSubnormal.step hKM hnorm hMsub,
    isQuasisimple_of_commutator_map hk hK hMmap hq⟩, ?_⟩
  rw [hK]
  exact map_commutator_eq_of hMmap hq

theorem le_GLALayer_of_map_le (π : G →* H) (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {X P : Subgroup G} (hPp : ⁅P, P⁆ = P) (hPL : P.map π ≤ GLALayer (X.map π)) :
    P ≤ GLALayer X := by
  have hL : GLALayer (X.map π) ≤ (GLALayer X).map π := by
    refine GLALayer_le_of fun Kb hKb => ?_
    obtain ⟨K, hKc, rfl⟩ := exists_component_lift π hk hKb
    exact Subgroup.map_mono (le_GLALayer hKc)
  have hPL' : P.map π ≤ (GLALayer X).map π := hPL.trans hL
  have hcomm : ⁅P, P⁆ ≤ GLALayer X := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 (hPL' (Subgroup.mem_map_of_mem π hx))
    obtain ⟨l', hl', hl'y⟩ := Subgroup.mem_map.1 (hPL' (Subgroup.mem_map_of_mem π hy))
    have hc : l⁻¹ * x ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hlx]; simp)
    have hc' : l'⁻¹ * y ∈ Subgroup.center G := hk _ (by rw [map_mul, map_inv, hl'y]; simp)
    have e : ⁅x, y⁆ = ⁅l * (l⁻¹ * x), l' * (l'⁻¹ * y)⁆ := by simp only [mul_inv_cancel_left]
    rw [e, comm_mul_central_left hc, comm_mul_central_right hc']
    exact commutatorElement_mem_of hl hl'
  rw [hPp] at hcomm
  exact hcomm

end Lift

end CFSG.LocalAnalysis.GLTheoremA.I142N
