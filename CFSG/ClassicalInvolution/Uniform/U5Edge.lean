module

public import CFSG.ClassicalInvolution.Uniform.U5G2D4
public import CFSG.ClassicalInvolution.Uniform.U3Thm7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups commutatorElement

section Block

variable {G : Type} [Group G]

theorem edgeless_or_connected_of_normalizers {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    {r : Subgroup G → Subgroup G → Prop}
    (hr : ∀ (g : G) (K J : Subgroup G), r K J → r (conjSub g K) (conjSub g J))
    (hsymm : ∀ K J : Subgroup G, r K J → r J K)
    (htop : ∀ K ∈ Ω, ∀ J ∈ Ω, r K J →
      Subgroup.normalizer (K : Set G) ⊔ Subgroup.normalizer (J : Set G) = ⊤) :
    (∀ K ∈ Ω, ∀ J ∈ Ω, ¬ r K J) ∨
      ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ r M N) K J := by
  by_cases hedge : ∃ K₀ ∈ Ω, ∃ J₀ ∈ Ω, r K₀ J₀
  · right
    obtain ⟨K₀, hK₀, J₀, hJ₀, hrJ⟩ := hedge
    set R : Subgroup G → Subgroup G → Prop := fun M N => N ∈ Ω ∧ r M N with hR
    set S : Set (Subgroup G) := {J | Relation.ReflTransGen R K₀ J} with hS
    have path_conj : ∀ (g : G) {A B : Subgroup G}, Relation.ReflTransGen R A B →
        Relation.ReflTransGen R (conjSub g A) (conjSub g B) := by
      intro g A B h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.tail ⟨hΩ g _ hbc.1, hr g _ _ hbc.2⟩
    have path_rev : ∀ {A B : Subgroup G}, A ∈ Ω → Relation.ReflTransGen R A B →
        B ∈ Ω ∧ Relation.ReflTransGen R B A := by
      intro A B hA h
      induction h with
      | refl => exact ⟨hA, Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        exact ⟨hbc.1, Relation.ReflTransGen.head ⟨ih.1, hsymm _ _ hbc.2⟩ ih.2⟩
    have mapS : ∀ g : G, conjSub g K₀ ∈ S → ∀ J ∈ S, conjSub g J ∈ S :=
      fun g hg J hJ => hg.trans (path_conj g hJ)
    have mem_stab : ∀ g : G, conjSub g K₀ ∈ S → conjSub g⁻¹ K₀ ∈ S → g ∈ conjStabilizer S := by
      intro g hg hg' J
      refine ⟨fun h => ?_, fun h => mapS g hg J h⟩
      have := mapS g⁻¹ hg' _ h
      rwa [conjSub_inv_conjSub] at this
    have hK₀S : K₀ ∈ S := Relation.ReflTransGen.refl
    have hJ₀S : J₀ ∈ S := Relation.ReflTransGen.single ⟨hJ₀, hrJ⟩
    have hN : Subgroup.normalizer (K₀ : Set G) ≤ conjStabilizer S := by
      intro n hn
      have h1 : conjSub n K₀ = K₀ := normalizer_iff_conjSub_eq.mp hn
      have h2 : conjSub n⁻¹ K₀ = K₀ := normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ hn)
      exact mem_stab n (by rw [h1]; exact hK₀S) (by rw [h2]; exact hK₀S)
    have hN' : Subgroup.normalizer (J₀ : Set G) ≤ conjStabilizer S := by
      have key : ∀ n ∈ Subgroup.normalizer (J₀ : Set G), conjSub n K₀ ∈ S := by
        intro n hn
        have h1 : conjSub n J₀ = J₀ := normalizer_iff_conjSub_eq.mp hn
        have h2 : r (conjSub n K₀) J₀ := by
          have := hr n K₀ J₀ hrJ
          rwa [h1] at this
        exact hJ₀S.tail ⟨hΩ n K₀ hK₀, hsymm _ _ h2⟩
      intro n hn
      exact mem_stab n (key n hn) (key n⁻¹ (Subgroup.inv_mem _ hn))
    have htopS : ∀ g : G, g ∈ conjStabilizer S := by
      intro g
      have : (⊤ : Subgroup G) ≤ conjStabilizer S := by
        rw [← htop K₀ hK₀ J₀ hJ₀ hrJ]
        exact sup_le hN hN'
      exact this (Subgroup.mem_top g)
    have hall : ∀ J ∈ Ω, J ∈ S := by
      intro J hJ
      obtain ⟨g, hg⟩ := htrans K₀ hK₀ J hJ
      rw [← hg]
      exact (htopS g K₀).mpr hK₀S
    intro K hK J hJ
    exact (path_rev hK₀ (hall K hK)).2.trans (hall J hJ)
  · left
    push Not at hedge
    exact fun K hK J hJ h => hedge K hK J hJ h

end Block

section Edge


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem uniqueInvolution_mem_normalizer_of_omegaNbr (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    {K J : Subgroup G} {zJ : G} (hzJ : IsUniqueInvolution J zJ) (hJ : J ∈ omegaNbr Ω K) :
    zJ ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := hJ
  obtain ⟨J', hJ'Ω, P, rfl⟩ := hR
  obtain ⟨z', hz'0⟩ := hΩ.classical J' hJ'Ω
  have hz' := hz'0.isUniqueInvolution_sl2
  have h2J' : 2 ∣ Nat.card J' := by
    have h := Subgroup.orderOf_dvd_natCard J' hz'.mem
    rwa [hz'0.orderOf_eq_two] at h
  have h2P : 2 ∣ Nat.card (P : Subgroup J') := by
    rw [Sylow.card_eq_multiplicity P]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp
      ((Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos (α := J')).ne' h2J')))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup J')) 2 h2P
  have hx2 : ((x : J') : G) * ((x : J') : G) = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg (fun y : ↥(P : Subgroup J') => (((y : J') : G))) h
  have hx1 : ((x : J') : G) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext (Subtype.ext h)
    rw [h', orderOf_one] at hx
    omega
  have hxR : ((x : J') : G) ∈ Subgroup.map J'.subtype (P : Subgroup J') := ⟨(x : J'), x.2, rfl⟩
  have hxzJ : ((x : J') : G) = zJ :=
    (hzJ.unique _ (hRJ hxR) hx2).resolve_left hx1
  rw [← hxzJ]
  exact hRN hxR

theorem normalizers_top_of_omegaNbr (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K)
    (hpair : ∀ u v : G, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) = ⊤)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaNbr Ω K) :
    Subgroup.normalizer (K : Set G) ⊔ Subgroup.normalizer (J : Set G) = ⊤ := by
  have hJΩ : J ∈ Ω := hJ.1
  have hne : J ≠ K := hJ.2.1
  have hconj := hΩ.conjInvariant
  obtain ⟨zK, hzK0⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ0⟩ := hΩ.classical J hJΩ
  have hzK := hzK0.isUniqueInvolution_sl2
  have hzJ := hzJ0.isUniqueInvolution_sl2
  have hCN : ∀ {L : Subgroup G} {z : G}, L ∈ Ω → IsUniqueInvolution L z →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro L z hL hz g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hgz : g * z * g⁻¹ = z := by
      calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hg]
        _ = z := by group
    have h1 : IsUniqueInvolution (conjSub g L) z := by
      have := hz.conj g
      rwa [hgz] at this
    have h2 : conjSub g L ∈ twinSet Ω L := ⟨hconj g L hL, z, hz, h1⟩
    exact normalizer_iff_conjSub_eq.mpr (hnt L hL _ h2)
  have hzJN := uniqueInvolution_mem_normalizer_of_omegaNbr hΩ hzJ hJ
  have hcomm : zJ * zK = zK * zJ := by
    have := conj_eq_of_mem_normalizer hzK hzJN
    calc zJ * zK = (zJ * zK * zJ⁻¹) * zJ := by group
      _ = zK * zJ := by rw [this]
  have hzne : zK ≠ zJ := by
    intro h
    exact hne (hnt K hK J ⟨hJΩ, zK, hzK, h ▸ hzJ⟩)
  have hpair' := hpair zK zJ hzK.sq hzJ.sq hzK.ne_one hzJ.ne_one hzne hcomm.symm
  rw [eq_top_iff, ← hpair']
  exact sup_le_sup (hCN hK hzK) (hCN hJΩ hzJ)

variable [IsSimpleGroup G]

theorem ih8G2D4EdgeU_of_g2NonToral_aux (h : G2NonToralGenerate3)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e) (ht : t = .G2 ∨ t = .trialityD4) :
    Disconnected.DEdgeless Ω ∨ Disconnected.DConnected Ω := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have hnt := noTwins_of_g2d4_datum M htrans ht
  have he1 : e = 1 := by
    rcases M.exp_eq with h' | ⟨-, h'⟩
    · exact h'
    · omega
  have hpairL : ∀ u v : (modelUniv t k 3 e Nat.prime_three).K, u * u = 1 → v * v = 1 → u ≠ 1 →
      v ≠ 1 → u ≠ v → u * v = v * u →
      Subgroup.centralizer ({u} : Set (modelUniv t k 3 e Nat.prime_three).K) ⊔
        Subgroup.centralizer ({v} : Set (modelUniv t k 3 e Nat.prime_three).K) = ⊤ := by
    rcases ht with rfl | rfl
    · obtain ⟨hk, -⟩ := M.admissible.2.2
      subst hk
      subst he1
      exact g2_pairGen3 h
    · have hk : k = 0 := M.admissible.2.2
      subst hk
      subst he1
      intro u v hu hv hu1 hv1 huv hcomm
      exact G2D4Models.sup_centralizer_eq_top_model_td4 hp2 M.admissible hu hv hu1 hv1 huv hcomm
  have hpairG : ∀ u v : G, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) = ⊤ := by
    intro u v hu hv hu1 hv1 huv hcomm
    obtain ⟨u₀, rfl⟩ := M.surj u
    obtain ⟨v₀, rfl⟩ := M.surj v
    have hu₀ : u₀ * u₀ = 1 := hinj (by rw [map_mul, hu, map_one])
    have hv₀ : v₀ * v₀ = 1 := hinj (by rw [map_mul, hv, map_one])
    have hPG := hpairL u₀ v₀ hu₀ hv₀ (fun h' => hu1 (by rw [h', map_one]))
      (fun h' => hv1 (by rw [h', map_one])) (fun h' => huv (by rw [h']))
      (hinj (by rw [map_mul, map_mul]; exact hcomm))
    have hle : ∀ (w : (modelUniv t k 3 e Nat.prime_three).K),
        (Subgroup.centralizer ({w} : Set (modelUniv t k 3 e Nat.prime_three).K)).map M.ψ ≤
          Subgroup.centralizer ({M.ψ w} : Set G) := by
      intro w y hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    rw [eq_top_iff]
    intro g _
    obtain ⟨g₀, rfl⟩ := M.surj g
    have hg₀ : g₀ ∈ Subgroup.centralizer ({u₀} : Set (modelUniv t k 3 e Nat.prime_three).K) ⊔
        Subgroup.centralizer ({v₀} : Set (modelUniv t k 3 e Nat.prime_three).K) := by
      rw [hPG]
      exact Subgroup.mem_top g₀
    have hmap : (Subgroup.centralizer ({u₀} : Set (modelUniv t k 3 e Nat.prime_three).K) ⊔
        Subgroup.centralizer ({v₀} : Set (modelUniv t k 3 e Nat.prime_three).K)).map M.ψ ≤
          Subgroup.centralizer ({M.ψ u₀} : Set G) ⊔ Subgroup.centralizer ({M.ψ v₀} : Set G) := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (hle u₀) (hle v₀)
    exact hmap ⟨g₀, hg₀, rfl⟩
  have hconj := hΩ.conjInvariant
  exact edgeless_or_connected_of_normalizers (r := Disconnected.dAdj Ω) hconj htrans
    (fun g K J h => by
      rcases h with h | h
      · exact Or.inl (omegaNbr_conj hconj h g)
      · exact Or.inr (omegaNbr_conj hconj h g))
    (fun K J h => Disconnected.dAdj_symm h)
    (fun K hK J hJ hadj => by
      rcases hadj with h' | h'
      · exact normalizers_top_of_omegaNbr hΩ hnt hpairG hK h'
      · rw [sup_comm]
        exact normalizers_top_of_omegaNbr hΩ hnt hpairG hJ h')

end Edge

section Main


theorem ih8G2D4EdgeU_of_g2NonToral (h : G2NonToralGenerate3) : Ih8G2D4EdgeU := by
  intro G _ _ _ Ω hΩ _ htrans t k e hMod ht
  obtain ⟨M⟩ := hMod
  exact ih8G2D4EdgeU_of_g2NonToral_aux h hΩ htrans M ht

end Main

end CFSG.ClassicalInvolution.Uniform
