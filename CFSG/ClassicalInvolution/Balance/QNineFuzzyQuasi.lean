module

public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Quasisimple

omit [Finite G] in
theorem isQuasisimple_of_mem_of_single_class
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {K₀ : Subgroup G} (hK₀ : K₀ ∈ Ω)
    (hq : CFSG.Open.IsQuasisimple K₀) : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J := by
  obtain ⟨K, -, hK⟩ := hsingle
  intro J hJ
  obtain ⟨g₀, rfl⟩ := hK K₀ hK₀
  obtain ⟨g, rfl⟩ := hK J hJ
  have h : conjSub g K = conjSub (g * g₀⁻¹) (conjSub g₀ K) := by
    rw [← conjSub_mul]
    simp
  rw [h]
  exact Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective _ (MulAut.conj (g * g₀⁻¹)).toMonoidHom
      (MulAut.conj (g * g₀⁻¹)).injective).symm hq

end Quasisimple

section Lifting

theorem inf_oddCoreIn_le_center_of_isQuasisimple {a : G} {X : Subgroup G}
    (hXq : CFSG.Open.IsQuasisimple X) (hXC : X ≤ Subgroup.centralizer ({a} : Set G)) {zX : G}
    (hzX : IsClassicalMember p f X zX) :
    ∀ u ∈ X ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)), ∀ y ∈ X, u * y = y * u := by
  set N : Subgroup G := oddCoreIn (Subgroup.centralizer ({a} : Set G)) with hNdef
  have hnorm : X ≤ Subgroup.normalizer ((X ⊓ N : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hkinv : k⁻¹ ∈ X := Subgroup.inv_mem _ hk
    have hkC := hXC hk
    have hkinvC := hXC hkinv
    constructor
    · rintro ⟨hs1, hs2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hs1) hkinv, conj_mem_oddCoreIn hkC hs2⟩
    · rintro ⟨hs1, hs2⟩
      have e : s = k⁻¹ * (k * s * k⁻¹) * k := by group
      rw [e]
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hkinv hs1) hk, ?_⟩
      have := conj_mem_oddCoreIn hkinvC hs2
      simpa [mul_assoc] using this
  have hN : ((X ⊓ N).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hnorm
  rcases Quasisimple.normal_le_center_or_eq_top hXq ((X ⊓ N).subgroupOf X) with hle | htop
  · intro u hu y hy
    have hu' : (⟨u, hu.1⟩ : X) ∈ (X ⊓ N).subgroupOf X := Subgroup.mem_subgroupOf.mpr hu
    have := Subgroup.mem_center_iff.mp (hle hu') ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  · exfalso
    have hz : (⟨zX, hzX.mem⟩ : X) ∈ (X ⊓ N).subgroupOf X := by rw [htop]; exact Subgroup.mem_top _
    exact hzX.ne_one (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _)
      (Subgroup.mem_subgroupOf.mp hz).2 (sq_eq_one hzX))

theorem centralizes_of_isQuasisimple_of_comm_mem_oddCoreIn (hΩ : InClass p f Ω)
    (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J) {a : G} {X : Subgroup G} (hX : X ∈ Ω)
    (hXC : X ≤ Subgroup.centralizer ({a} : Set G)) {zX : G} (hzX : IsClassicalMember p f X zX)
    {g : G} (hgz : g * zX * g⁻¹ = zX)
    (hcomm : ∀ y ∈ X, g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G))) :
    ∀ y ∈ X, g * y = y * g := by
  have hgXΩ : conjSub g X ∈ Ω := hΩ.conjInvariant g X hX
  have hz'' : IsClassicalMember p f (conjSub g X) zX := by
    have := hzX.conj g
    rwa [hgz] at this
  rcases members_eq_or_commute hz'' hzX (hqs _ hgXΩ) (hqs _ hX) with heq | hc
  ·
    have hnorm : ∀ y ∈ X, g * y * g⁻¹ ∈ X := fun y hy => heq ▸ conj_mem_conjSub hy
    have hcen := inf_oddCoreIn_le_center_of_isQuasisimple (hqs X hX) hXC hzX
    set e : G → G := fun y => g * y * g⁻¹ * y⁻¹ with he_def
    have he : ∀ y ∈ X, e y ∈ X ⊓ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := fun y hy =>
      ⟨Subgroup.mul_mem _ (hnorm y hy) (Subgroup.inv_mem _ hy), hcomm y hy⟩
    have hemul : ∀ y₁ ∈ X, ∀ y₂ ∈ X, e (y₁ * y₂) = e y₁ * e y₂ := by
      intro y₁ hy₁ y₂ hy₂
      have h2 : e y₂ * y₁ = y₁ * e y₂ := hcen _ (he y₂ hy₂) y₁ hy₁
      have h3 : y₁ * e y₂ * y₁⁻¹ = e y₂ := by
        rw [← h2]
        group
      calc e (y₁ * y₂) = (g * y₁ * g⁻¹ * y₁⁻¹) * (y₁ * (g * y₂ * g⁻¹ * y₂⁻¹) * y₁⁻¹) := by
            simp only [he_def]
            group
        _ = e y₁ * e y₂ := by
            have h4 : y₁ * (g * y₂ * g⁻¹ * y₂⁻¹) * y₁⁻¹ = g * y₂ * g⁻¹ * y₂⁻¹ := h3
            rw [h4]
    let φ : X →* X := MonoidHom.mk' (fun y => ⟨e y.1, (he y.1 y.2).1⟩)
      (fun a b => Subtype.ext (hemul a.1 a.2 b.1 b.2))
    have hφc : ∀ y, φ y ∈ Subgroup.center X := fun y =>
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hcen _ (he y.1 y.2) x.1 x.2).symm
    let ψ : X →* Subgroup.center X := φ.codRestrict (Subgroup.center X) hφc
    have hperf : commutator X = ⊤ := by
      have := hzX.perfect
      exact Group.IsPerfect.commutator_eq_top
    have hker : commutator X ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
    rw [hperf] at hker
    intro y hy
    have h1 : ψ ⟨y, hy⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
    have h2 : e y = 1 := congrArg (fun w : Subgroup.center X => ((w : X) : G)) h1
    calc g * y = (g * y * g⁻¹ * y⁻¹) * y * g := by group
      _ = y * g := by
        change e y * y * g = y * g
        rw [h2]
        group
  · exfalso
    have hperf : ⁅X, X⁆ = X := by
      have := hzX.perfect
      exact Subgroup.commutator_eq_self
    have hle : X ≤ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
      rw [← hperf]
      refine Subgroup.commutator_le.mpr fun k₁ hk₁ k₂ hk₂ => ?_
      have hcm := hcomm k₁ hk₁
      have hconj := conj_mem_oddCoreIn (hXC hk₂) hcm
      have h2 := hc _ (conj_mem_conjSub hk₁) k₂ hk₂
      have h3 : (g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹) = k₂ := by
        calc _ = (g * k₁ * g⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹)) := by group
          _ = (g * k₁ * g⁻¹)⁻¹ * ((g * k₁ * g⁻¹) * k₂) := by rw [h2]
          _ = k₂ := by group
      have e : ⁅k₁, k₂⁆ = (g * k₁ * g⁻¹ * k₁⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹ * k₁⁻¹) * k₂⁻¹) := by
        calc ⁅k₁, k₂⁆ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := rfl
          _ = k₁ * ((g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹)) * k₁⁻¹ * k₂⁻¹ := by rw [h3]
          _ = _ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcm) hconj
    exact hzX.ne_one (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn _) (hle hzX.mem)
      (sq_eq_one hzX))

end Lifting

section Extension

theorem exists_extension_of_untouched_of_isQuasisimple (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A)) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) {K : Subgroup G} (hK : K ∈ centMembers Ω a)
    (hKL : ∀ L ∈ frameFamily p f Ω A, ¬ InCommonComponent a K L) :
    ∃ M ∈ Ω, M ≤ Subgroup.centralizer (A : Set G) ∧
      (∃ z : G, IsClassicalMember p f M z ∧ z ∉ A) ∧ InCommonComponent a K M ∧
        ∀ L ∈ frameFamily p f Ω A, Commutes L M := by
  classical
  obtain ⟨Q, hQ, hi, hgen⟩ :=
    exists_centralized_component_of_not_inCommonComponent hp2 hΩ hIH hM ha hnc hK hKL
  have hcom : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hM.elem.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hAC : ∀ {x : G}, x ∈ A → x ∈ Subgroup.centralizer ({a} : Set G) := fun hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcom hx ha)
  have hFC : ∀ {L : Subgroup G}, L ∈ frameFamily p f Ω A →
      L ≤ Subgroup.centralizer ({a} : Set G) := fun hL =>
    hL.2.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hM.card]; norm_num)
  have hcommN : ∀ x ∈ A, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈
      oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx k hk
    have hkC : k ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hkC).mp
      (hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC)))
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
  have hzC : z ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hz.mem
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (sq_eq_one hz)
  obtain ⟨n, hnN, hfix⟩ := exists_conj_fixed_of_isPGroup (A := A)
    (N := oddCoreIn (Subgroup.centralizer ({a} : Set G))) hApg
    (odd_card_oddCoreIn _) (fun x hx m hm => conj_mem_oddCoreIn (hAC hx) hm) (sq_eq_one hz)
    (fun m hm => conj_mem_oddCoreIn hzC hm) (by
      intro x hx
      have h1 := (oddCoreIn _).inv_mem (hcommN x hx z hz.mem)
      have e : z * (x * z * x⁻¹) = (x * z * x⁻¹ * z⁻¹)⁻¹ := by
        have h2 : (x * z * x⁻¹ * z⁻¹)⁻¹ = z * x * z⁻¹ * x⁻¹ := by group
        rw [h2, hzinv]
        group
      rw [e]
      exact h1)
  have hnC : n ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hnN
  have hn1 : oddQuotMk a ⟨n, hnC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn hnN hnC
  have hK'Ω : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK.1
  have hK'C : conjSub n K ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    have h1 : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have e : y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC (hK.2 h1)) (Subgroup.inv_mem _ hnC)
  have hz' : IsClassicalMember p f (conjSub n K) (n * z * n⁻¹) := hz.conj n
  have himg : ∀ (y : G) (hy : y ∈ conjSub n K) (hyC : y ∈ Subgroup.centralizer ({a} : Set G)),
      ∃ k ∈ K, ∃ hkC : k ∈ Subgroup.centralizer ({a} : Set G),
        oddQuotMk a ⟨y, hyC⟩ = oddQuotMk a ⟨k, hkC⟩ := by
    intro y hy hyC
    have hk : n⁻¹ * y * n ∈ K := mem_conjSub_iff.mp hy
    have hkC : n⁻¹ * y * n ∈ Subgroup.centralizer ({a} : Set G) := hK.2 hk
    refine ⟨n⁻¹ * y * n, hk, hkC, ?_⟩
    have e : (⟨y, hyC⟩ : Subgroup.centralizer ({a} : Set G)) =
        ⟨n, hnC⟩ * ⟨n⁻¹ * y * n, hkC⟩ * ⟨n, hnC⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
    rw [e, map_mul, map_mul, map_inv, hn1]
    simp
  have hcommN' : ∀ x ∈ A, ∀ y ∈ conjSub n K,
      x * y * x⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    intro x hx y hy
    have hyC := hK'C hy
    obtain ⟨k, hk, hkC, hyk⟩ := himg y hy hyC
    refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) (hAC hx) hyC).mp ?_
    have h1 := hgen x hx (hAC hx) _ (hi (oddQuotMk_mem_modOdd hk hkC))
    rw [← hyk] at h1
    exact h1
  have hKcent : conjSub n K ≤ Subgroup.centralizer (A : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    exact centralizes_of_isQuasisimple_of_comm_mem_oddCoreIn hΩ hqs hK'Ω hK'C hz' (hfix x hxA)
      (fun y' hy' => hcommN' x hxA y' hy') y hy
  have hMQ : modOdd a (conjSub n K) ≤ Q := by
    rintro _ ⟨y', hy', rfl⟩
    obtain ⟨k, hk, hkC, hyk⟩ := himg (y' : G) hy' y'.2
    show oddQuotMk a ⟨(y' : G), y'.2⟩ ∈ Q
    rw [hyk]
    exact hi (oddQuotMk_mem_modOdd hk hkC)
  refine ⟨conjSub n K, hK'Ω, hKcent, ⟨n * z * n⁻¹, hz', fun hzA => ?_⟩, ⟨Q, hQ, hi, hMQ⟩, ?_⟩
  ·
    exact hKL (conjSub n K) ⟨hK'Ω, hKcent, _, hzA, hz'⟩ ⟨Q, hQ, hi, hMQ⟩
  ·
    intro L hL l hl g hg
    have hLΩ : L ∈ Ω := hL.1
    obtain ⟨zL, hzLA, hzL⟩ := hL.2.2
    have hgC := hK'C hg
    obtain ⟨k, hk, hkC, hgk⟩ := himg g hg hgC
    have hcomm' : ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
      intro y hy
      have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := hFC hL hy
      have hky := comm_mem_oddCoreIn_of_not_inCommonComponent hp2 hΩ hIH hnc hK
        ⟨hLΩ, hFC hL⟩ (hKL L hL) k hk y hy
      have h1 : oddQuotMk a ⟨k, hkC⟩ * oddQuotMk a ⟨y, hyC⟩ =
          oddQuotMk a ⟨y, hyC⟩ * oddQuotMk a ⟨k, hkC⟩ :=
        (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hkC hyC).mpr hky
      rw [← hgk] at h1
      exact (mk_comm_eq_iff (Y := Subgroup.centralizer ({a} : Set G)) hgC hyC).mp h1
    have hgz : g * zL * g⁻¹ = zL :=
      (Subgroup.mem_centralizer_iff.mp (hKcent hg) zL hzLA).symm ▸ by group
    exact (centralizes_of_isQuasisimple_of_comm_mem_oddCoreIn hΩ hqs hLΩ (hFC hL) hzL hgz hcomm' l
      hl).symm

end Extension

section Frames

theorem exists_covering_frame_of_indepTriple_pair_of_isQuasisimple (hp2 : p ≠ 2) (hf : 0 < f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J) {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {i j : Fin 3} (hij : i ≠ j) {x : G} (hxA : x ∈ A)
    (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) {K' : Subgroup G} (hK' : K' ∈ centMembers Ω x) :
    (∃ L ∈ frameFamily p f Ω A, InCommonComponent x K' L) ∨
      ∃ A' : Subgroup G, IndepTripleOn p f Ω A' ∧ Subgroup.closure ({z i, z j} : Set G) ≤ A' ∧
        Nat.card (Subgroup.closure ({z i, z j} : Set G)) = 4 ∧
          ∃ L ∈ frameFamily p f Ω A', InCommonComponent x K' L := by
  have hA : IndepTripleOn p f Ω A := ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩
  have hMF := memberFamily_of_indepTripleOn hp2 hf hA
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hKfam : ∀ m, K m ∈ frameFamily p f Ω A := fun m =>
    ⟨(hK m).1, by rw [hAdef]; exact triple_centralizes hK hcomm m, z m, hzA m, (hK m).2⟩
  by_cases hcc : ∃ L ∈ frameFamily p f Ω A, InCommonComponent x K' L
  · exact Or.inl hcc
  · push Not at hcc
    obtain ⟨M, hMΩ, hMA, ⟨zM, hzM, hzMA⟩, hKM, hMcomm⟩ :=
      exists_extension_of_untouched_of_isQuasisimple hp2 hΩ hIH hqs hMF hxA hnc hK' hcc
    obtain ⟨hA', hF4, hMA'⟩ := indepTripleOn_exchange hK hcomm hAdef hel hcard hij hMΩ hzM hMA
      hzMA (hMcomm (K i) (hKfam i)) (hMcomm (K j) (hKfam j))
    refine Or.inr ⟨Subgroup.closure ({z i, z j, zM} : Set G), hA', ?_, hF4, M,
      ⟨hMΩ, hMA', zM, Subgroup.subset_closure (by simp), hzM⟩, hKM⟩
    rw [Subgroup.closure_le]
    rintro _ (rfl | hy)
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.subset_closure (by simp)

theorem exists_frame_of_indepTriple_pair_of_isQuasisimple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {F₀ : Subgroup G} (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A)
    (hα : alphaCore F₀ = ⊥) {i j : Fin 3} (hij : i ≠ j) {x : G}
    (hx : x ∈ Subgroup.closure ({z i, z j} : Set G)) (hx1 : x ≠ 1) {K' : Subgroup G}
    (hK' : K' ∈ centMembers Ω x) :
    ∃ A' : Subgroup G, IndepTripleOn p f Ω A' ∧ x ∈ A' ∧
      (∀ F ∈ signalizerFunctorEk 2 2 A', deltaCore F = ⊥) ∧
        ∃ L ∈ frameFamily p f Ω A', InCommonComponent x K' L := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hA : IndepTripleOn p f Ω A := ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩
  have hB : RankThreeBalance A :=
    rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hA (hlay A hA)
  have hΔA : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
    deltaCore_eq_bot_of_alphaCore_eq_bot hB hF₀ hα
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hFA : Subgroup.closure ({z i, z j} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | hy)
    · exact hzA i
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzA j
  rcases exists_covering_frame_of_indepTriple_pair_of_isQuasisimple hp2 hf hΩ hIH hqs hK hcomm
      hAdef hel hcard hij (hFA hx) (not_subset_center_of_ne_one hnab hx1) hK' with
    hcc | ⟨A', hA', hFA', hF4, hcc⟩
  · exact ⟨A, hA, hFA hx, hΔA, hcc⟩
  · have hB' : RankThreeBalance A' := rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ
      hIH hA' (hlay A' hA')
    have hFE : Subgroup.closure ({z i, z j} : Set G) ∈ signalizerFunctorEk 2 2 A :=
      ⟨hFA, by rw [hF4]; norm_num⟩
    have hFE' : Subgroup.closure ({z i, z j} : Set G) ∈ signalizerFunctorEk 2 2 A' :=
      ⟨hFA', by rw [hF4]; norm_num⟩
    have hαF : alphaCore (Subgroup.closure ({z i, z j} : Set G)) = ⊥ :=
      (alphaFrame_eq_alphaCore hB hFE).symm.trans ((alphaFrame_eq_alphaCore hB hF₀).trans hα)
    exact ⟨A', hA', hFA' hx, deltaCore_eq_bot_of_alphaCore_eq_bot hB' hFE' hαF, hcc⟩

theorem localOddCentral_of_indepTriple_pair_of_isQuasisimple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {F₀ : Subgroup G} (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A)
    (hα : alphaCore F₀ = ⊥) {i j : Fin 3} (hij : i ≠ j) {x : G}
    (hx : x ∈ Subgroup.closure ({z i, z j} : Set G)) (hx1 : x ≠ 1) :
    LocalOddCentral Ω {x} :=
  localOddCentral_of_framesMeet hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH
    hx1 fun K' hK' => by
      obtain ⟨A', hA', hxA', hΔ, L, ⟨hLΩ, hLA, zL, hzLA, hzL⟩, hcc⟩ :=
        exists_frame_of_indepTriple_pair_of_isQuasisimple hnab hp2 hq hΩ hIH hqs hlay hK hcomm
          hAdef hel hcard hF₀ hα hij hx hx1 hK'
      obtain ⟨K'', z'', hK'', hcomm'', hdef'', hel'', hcard''⟩ := hA'
      exact ⟨A', hdef'' ▸ hel'', hdef'' ▸ hcard'', hΔ, hxA', L, hLΩ, zL, hzLA, hzL, hLA, hcc⟩

theorem triangleFramesMeetAt_of_indepTriple_pair_of_isQuasisimple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J)
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) {i j : Fin 3} (hij : i ≠ j) {x : G}
    (hx : x ∈ Subgroup.closure ({z i, z j} : Set G)) (hx1 : x ≠ 1) :
    TriangleFramesMeetAt p f Ω x := by
  have hA : IndepTripleOn p f Ω A := ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩
  have hzA : ∀ m, z m ∈ A := fun m => hAdef ▸ Subgroup.subset_closure ⟨m, rfl⟩
  have hFA : Subgroup.closure ({z i, z j} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | hy)
    · exact hzA i
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzA j
  intro K' hK'
  rcases exists_covering_frame_of_indepTriple_pair_of_isQuasisimple hp2 hf hΩ hIH hqs hK hcomm
      hAdef hel hcard hij (hFA hx) (not_subset_center_of_ne_one hnab hx1) hK' with
    hcc | ⟨A', hA', hFA', -, hcc⟩
  · exact ⟨A, hA, hFA hx, hcc⟩
  · exact ⟨A', hA', hFA' hx, hcc⟩

end Frames

section Delta

theorem isQuasisimple_of_member_of_deltaCore_eq_bot [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {K : Subgroup G} {z : G} (hKΩ : K ∈ Ω)
    (hz : IsClassicalMember p f K z) {F : Subgroup G} (hF : IsElemAbelian 2 F)
    (hKF : K ≤ Subgroup.centralizer (F : Set G)) (hΔ : deltaCore F = ⊥) :
    CFSG.Open.IsQuasisimple K := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hW : WeakMember (GaloisField p f) K z :=
    ⟨hz.orderOf_eq_two, hz.mem, hz.perfect, hz.subnormal, hz.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hzF : ∀ x ∈ F, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hKF hz.mem) x hx).symm
  have hFC : F ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzF x hx).symm
  have hsub : IsSubnormal K (C ⊓ Subgroup.centralizer (F : Set G)) := by
    have h := isSubnormal_inf hz.subnormal (C ⊓ Subgroup.centralizer (F : Set G))
    rwa [inf_eq_left.mpr (le_inf (isSubnormal_le hz.subnormal) hKF),
      inf_eq_right.mpr inf_le_left] at h
  refine isQuasisimple_of_deltaCore_eq_bot_layer hz.subnormal hmem.perfect hmem.quasisimple hF
    hFC hKF hΔ hsub ?_
  intro f₀ hf₀ hf₀1 M hM
  exact hB_of_localLieSystems hp2 ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hKΩ
    hz.isCentralInvolution (not_subset_center_of_ne_one hnab hf₀1)
    (hKF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₀))) (hzF f₀ hf₀) M hM

end Delta

end CFSG.ClassicalInvolution.Balance.Theorem5
