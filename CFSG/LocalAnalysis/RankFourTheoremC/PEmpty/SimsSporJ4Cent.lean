module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Frob
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZK
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Facts
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4

open CFSG.Sporadic.J4 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Certificates

theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  have hx := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set G))
  have hy := Subgroup.card_mul_index (Subgroup.centralizer ({y} : Set G))
  rw [Subgroup.index_centralizer_eq_ncard, h.conjugatesOf_eq,
    ← Subgroup.index_centralizer_eq_ncard] at hx
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (hx.trans hy.symm)

theorem no_inv_commute
    (hF : J4Facts) {z : CFSG.Sporadic.J4.J} {p : ℕ} (hz : orderOf z = p)
    (h1 : ¬ p ∣ 1816657920) (h3 : ¬ p ∣ 21799895040) :
    ∀ t : CFSG.Sporadic.J4.J, orderOf t = 2 → t * z ≠ z * t := by
  intro t ht htz
  have hsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, sq] at h
    exact h
  have hne : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    norm_num at ht
  have hzC : z ∈ Subgroup.centralizer ({t} : Set CFSG.Sporadic.J4.J) := by
    have h := (Subgroup.mem_centralizer_singleton_iff (g := t) (k := z)).mpr htz.symm
    exact h
  have hdvd : p ∣ Nat.card (Subgroup.centralizer ({t} : Set CFSG.Sporadic.J4.J)) := by
    have h := Subgroup.orderOf_dvd_natCard _ hzC
    rw [hz] at h
    exact h
  rcases QT.inv_conj_root hF hsq hne with h | h
  · rw [← card_centralizer_eq_of_isConj h, CFSG.QuasithinUnique.A5.card_centralizer_eta_one] at hdvd
    exact h1 hdvd
  · rw [← card_centralizer_eq_of_isConj h, QT2.card_centralizer_eta_three] at hdvd
    exact h3 hdvd

theorem comm_duadSwap {σ : Equiv.Perm (Fin 24)} (h4 : σ 4 = 4 ∨ σ 4 = 11)
    (h11 : σ 11 = 4 ∨ σ 11 = 11) : σ * duadSwap = duadSwap * σ := by
  have key : Equiv.swap (σ 4) (σ 11) = Equiv.swap 4 11 := by
    rcases h4 with h4 | h4 <;> rcases h11 with h11 | h11
    · exact absurd (σ.injective (h4.trans h11.symm)) (by decide)
    · rw [h4, h11]
    · rw [h4, h11, Equiv.swap_comm]
    · exact absurd (σ.injective (h4.trans h11.symm)) (by decide)
  have h := Equiv.swap_apply_apply σ 4 11
  rw [key] at h
  unfold duadSwap
  calc σ * Equiv.swap 4 11 = σ * Equiv.swap 4 11 * σ⁻¹ * σ := by group
    _ = Equiv.swap 4 11 * σ := by rw [← h]

private theorem starHom_apply
    (g : Hj) (i : Fin 24) : starHom g i = starMap g i := rfl

theorem card_centralizer_le
    (hF : J4Facts) {u : CFSG.Sporadic.J4.J} {k : ℕ} (hk : u ^ k = QT.eta QT.uJ 11 1) {col : ℕ → ℕ}
    (hcol : ∀ j < 11, u * QT.uJ j * u⁻¹ = QT.eta QT.uJ 11 (col j)) (hcol_lt : ∀ j, col j < 2 ^ 11)
    {π : Equiv.Perm (Fin 24)}
    (hπ : ∀ i : Fin 24, ∀ c ∈ starMasks.getD i [], QT.rowsXor col 11 c ∈ starMasks.getD (π i) [])
    (hone : ∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11)
    (h4 : 1 ∈ starMasks.getD 4 []) (h11 : 1 ∈ starMasks.getD 11 []) :
    Nat.card (Subgroup.centralizer ({u} : Set CFSG.Sporadic.J4.J)) ≤
      ((Finset.range 2048).filter fun c => QT.rowsXor col 11 c = c).card *
      Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 // (σ : Equiv.Perm (Fin 24)) * π = π * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} := by
  classical
  have hM := hF.mat
  have hElem := QT.elem_uJ hM
  set C := Subgroup.centralizer ({u} : Set CFSG.Sporadic.J4.J) with hC
  have hcommC : ∀ x ∈ C, x * u = u * x := fun x hx => by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact h
  have hpow : ∀ x ∈ C, ∀ n : ℕ, x * u ^ n = u ^ n * x := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero, mul_one, one_mul]
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hcommC x hx, ← mul_assoc]
  have hcommη : ∀ x ∈ C, x * QT.eta QT.uJ 11 1 = QT.eta QT.uJ 11 1 * x := by
    intro x hx
    rw [← hk]
    exact hpow x hx k
  have hCH : C ≤ Hj := fun x hx =>
    QT2.centralizer_le_Hj_of_T hF QT2.one_mem_tMasks (hcommη x hx)
  have huC : u ∈ C := by
    have h := (Subgroup.mem_centralizer_singleton_iff (g := u) (k := u)).mpr rfl
    exact h
  have hconj : ∀ c, u * QT.eta QT.uJ 11 c * u⁻¹ = QT.eta QT.uJ 11 (QT.rowsXor col 11 c) :=
    fun c => QT.conj_eta hElem u col hcol le_rfl c
  have hπu : starHom ⟨u, hCH huC⟩ = π := by
    ext i
    rw [starHom_apply]
    exact congrArg Fin.val (starMap_eq (fun c hc => ⟨_, hπ i c hc, hconj c⟩))
  let ψ : C →* Equiv.Perm (Fin 24) := starHom.comp (Subgroup.inclusion hCH)
  have hψ : ∀ x : C, ψ x = starHom ⟨x, hCH x.2⟩ := fun x => rfl
  set F := (Finset.range 2048).filter fun c => QT.rowsXor col 11 c = c with hFdef
  have hker : ∀ x ∈ ψ.ker, ((x : C) : CFSG.Sporadic.J4.J) ∈ F.image (QT.eta QT.uJ 11) := by
    intro x hx
    have hxE : Subgroup.inclusion hCH x ∈ starHom.ker := hx
    rw [ker_starHom, Subgroup.mem_subgroupOf] at hxE
    obtain ⟨c, hc, hxc⟩ := (QT.mem_Eg_iff hElem).mp hxE
    have hxc' : ((x : C) : CFSG.Sporadic.J4.J) = QT.eta QT.uJ 11 c := hxc
    refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by simpa using hc), ?_⟩, hxc'.symm⟩
    have h1 := hconj c
    have hux : u * QT.eta QT.uJ 11 c * u⁻¹ = QT.eta QT.uJ 11 c := by
      rw [← hxc']
      calc u * ((x : C) : CFSG.Sporadic.J4.J) * u⁻¹ = (u * ((x : C) : CFSG.Sporadic.J4.J)) * u⁻¹ := rfl
        _ = (((x : C) : CFSG.Sporadic.J4.J) * u) * u⁻¹ := by rw [hcommC _ x.2]
        _ = ((x : C) : CFSG.Sporadic.J4.J) := by group
    rw [hux] at h1
    exact (QT.eta_inj hM c hc _ (QT.rowsXor_lt (fun j _ => hcol_lt j) le_rfl c) h1).symm
  have hkercard : Nat.card ψ.ker ≤ F.card := by
    set S := F.image (QT.eta QT.uJ 11) with hS
    have hinj : Function.Injective (fun x : ψ.ker => (⟨((x : C) : CFSG.Sporadic.J4.J), hker x x.2⟩ : S)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun s : S => (s : CFSG.Sporadic.J4.J)) hxy))
    calc Nat.card ψ.ker ≤ Nat.card S := Nat.card_le_card_of_injective _ hinj
      _ = S.card := Nat.card_eq_finsetCard S
      _ ≤ F.card := Finset.card_image_le
  have hfix : ∀ x : C, ∀ i : Fin 24, (i = 4 ∨ i = 11) →
      (starHom ⟨x, hCH x.2⟩ i = 4 ∨ starHom ⟨x, hCH x.2⟩ i = 11) := by
    intro x i hi
    rw [starHom_apply]
    have h1 : 1 ∈ starMasks.getD i [] := by
      rcases hi with rfl | rfl
      · exact h4
      · exact h11
    obtain ⟨c', hc', hxc⟩ := starMap_spec ⟨x, hCH x.2⟩ i 1 h1
    have hx1 : ((x : C) : CFSG.Sporadic.J4.J) * QT.eta QT.uJ 11 1 * ((x : C) : CFSG.Sporadic.J4.J)⁻¹ = QT.eta QT.uJ 11 1 := by
      rw [hcommη _ x.2]
      group
    have hc'1 : c' = 1 := QT.eta_inj hM c' (mem_star_lt (starMap ⟨x, hCH x.2⟩ i).2 hc') 1
      (by norm_num) (hxc.symm.trans hx1)
    rw [hc'1] at hc'
    rcases hone _ (starMap ⟨x, hCH x.2⟩ i).2 hc' with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hrange : ∀ σ ∈ ψ.range, σ ∈ CFSG.Blueprint.NativeSporadic.M24 ∧ σ * π = π * σ ∧
      σ * duadSwap = duadSwap * σ := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have hmem : ψ x ∈ starHom.range := ⟨_, rfl⟩
      rw [range_starHom] at hmem
      exact (Subgroup.closure_le _).mpr
        (by rintro _ (rfl | rfl | rfl) <;> exact tauOf_mem (by norm_num)) hmem
    · have hψu : ψ ⟨u, huC⟩ = π := hπu
      have hxu : x * ⟨u, huC⟩ = ⟨u, huC⟩ * x := Subtype.ext (hcommC _ x.2)
      rw [← hψu, ← map_mul, hxu, map_mul]
    · rw [hψ]
      exact comm_duadSwap (hfix x 4 (Or.inl rfl)) (hfix x 11 (Or.inr rfl))
  have hrangecard : Nat.card ψ.range ≤ Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * π = π * σ ∧ (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} := by
    refine Nat.card_le_card_of_injective
      (fun σ : ψ.range => ⟨⟨σ, (hrange σ σ.2).1⟩, (hrange σ σ.2).2⟩) ?_
    intro σ τ h
    exact Subtype.ext (congrArg (fun s => ((s.1 : CFSG.Blueprint.NativeSporadic.M24) :
      Equiv.Perm (Fin 24))) h)
  have hcard : Nat.card C = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  rw [hcard]
  exact Nat.mul_le_mul hkercard hrangecard

theorem row_of_rowFacts
    {p m n ce gam : ℕ} {col : ℕ → ℕ} {π : Equiv.Perm (Fin 24)} {z u : CFSG.Sporadic.J4.J} {L : List CFSG.Sporadic.J4.J}
    (hR : RowFactsJ p m n col (ce * gam) z u L) (hcol_lt : ∀ j, col j < 2 ^ 11)
    (hπ : ∀ i : Fin 24, ∀ c ∈ starMasks.getD i [],
      QT.rowsXor col 11 c ∈ starMasks.getD (π i) [])
    (hone : ∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11)
    (h4 : 1 ∈ starMasks.getD 4 []) (h11 : 1 ∈ starMasks.getD 11 [])
    (hce : ((Finset.range 2048).filter fun c => QT.rowsXor col 11 c = c).card = ce)
    (hgam : Nat.card {σ : CFSG.Blueprint.NativeSporadic.M24 //
      (σ : Equiv.Perm (Fin 24)) * π = π * σ ∧
        (σ : Equiv.Perm (Fin 24)) * duadSwap = duadSwap * σ} = gam)
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (hm : ∀ k, 0 < k → k < n → (m : ZMod p) ^ k ≠ 1)
    (h1 : ¬ p ∣ 1816657920) (h3 : ¬ p ∣ 21799895040)
    (hsyl : ¬ p ^ 2 ∣ 86775571046077562880) :
    FongSporLocal.KFactSporLocalRow .J4 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have hX : Nonempty (↥CFSG.Sporadic.J4.J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group) := ⟨(seedEquiv hM).symm.trans b⟩
  have hz : orderOf z = p := orderOf_eq_prime hR.z_pow hR.z_ne
  have hsylJ : ¬ p ^ 2 ∣ Nat.card ↥CFSG.Sporadic.J4.J := by
    rw [card_J hF]
    exact hsyl
  have hinv : ∀ t : CFSG.Sporadic.J4.J, orderOf t = 2 → t * z ≠ z * t := no_inv_commute hF hz h1 h3
  have hbad : ∀ e : CFSG.Sporadic.J4.J, e * u = u * e → orderOf e = 2 →
      ∃ i : ℕ, e * (z ^ i * e * z⁻¹ ^ i) ≠ (z ^ i * e * z⁻¹ ^ i) * e := by
    intro e heu he
    have hbound := card_centralizer_le hF hR.u_half hR.cols hcol_lt hπ hone h4 h11
    rw [hce, hgam, ← hR.length] at hbound
    have hsub : {x | x ∈ L} ⊆ (Subgroup.centralizer ({u} : Set CFSG.Sporadic.J4.J) : Set CFSG.Sporadic.J4.J) := by
      intro x hx
      have h := (Subgroup.mem_centralizer_singleton_iff (g := u) (k := x)).mpr (hR.comm x hx)
      exact h
    have hncard : ({x | x ∈ L} : Set CFSG.Sporadic.J4.J).ncard = L.length := by
      classical
      rw [show ({x | x ∈ L} : Set CFSG.Sporadic.J4.J) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
        List.toFinset_card_of_nodup hR.nodup]
    have heq : {x | x ∈ L} = (Subgroup.centralizer ({u} : Set CFSG.Sporadic.J4.J) : Set CFSG.Sporadic.J4.J) := by
      refine Set.eq_of_subset_of_ncard_le hsub ?_
      rw [hncard, ← Nat.card_coe_set_eq]
      exact hbound
    have heC : e ∈ (Subgroup.centralizer ({u} : Set CFSG.Sporadic.J4.J) : Set CFSG.Sporadic.J4.J) := by
      have h := (Subgroup.mem_centralizer_singleton_iff (g := u) (k := e)).mpr heu
      exact h
    rw [← heq] at heC
    rcases hR.inv e heC with h | h | h
    · rw [h, orderOf_one] at he
      norm_num at he
    · refine absurd ?_ h
      have h2 := pow_orderOf_eq_one e
      rw [he, sq] at h2
      exact h2
    · exact ⟨1, by simpa only [pow_one] using h⟩
  refine FongSporLocal.row_of_orbitU (↥CFSG.Sporadic.J4.J) (z₀ := z) (u₀ := u) (m := m) (n := n) ?_ hp
    hp2 ?_ ?_ hn ?_ ?_ hm ?_ ?_
  · exact hX
  · exact hsylJ
  · exact hz
  · exact hR.conj
  · exact hR.u_pow
  · exact hinv
  · exact hbad

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4
