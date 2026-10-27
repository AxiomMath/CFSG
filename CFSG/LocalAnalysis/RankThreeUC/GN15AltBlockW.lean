module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockI532
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlock

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbedding CFSG.RankThree.PartTwo Equiv
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound (le_closure_odd_of_isShort2 mem_normalizer_sup)
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (altHeart_irreducible)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

section Section

variable {V₀ K : Subgroup X} {n : ℕ}

omit [Finite X] in
theorem surjective_of_ne_bot (h5 : 5 ≤ n) {Φ : ↥K →* alternatingGroup (Fin n)}
    (hS : AltBaumSetup V₀ K Φ) {π : ↥⁅V₀, K⁆ →* Multiplicative (altHeart n)}
    (hπk : ∀ u, π u = 1 → ∀ k ∈ K, (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : ↥K) (u u' : ↥⁅V₀, K⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') =
        (QuotientAddGroup.mk (evenWeightPerm (Φ l : Perm (Fin n)) x) : altHeart n))
    (hne : ⁅V₀, K⁆ ≠ ⊥) : Function.Surjective π := by
  let S : AddSubgroup (altHeart n) := AddSubgroup.toSubgroup'.symm π.range
  have hmem : ∀ v : altHeart n, v ∈ S ↔ ∃ u, π u = Multiplicative.ofAdd v := fun v =>
    ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩
  have hinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n,
      (QuotientAddGroup.mk x : altHeart n) ∈ S →
        (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) ∈ S := by
    intro σ hσ x hx
    obtain ⟨u, hu⟩ := (hmem _).1 hx
    obtain ⟨k, hk⟩ := hS.surj ⟨σ, hσ⟩
    have hk2 : (Φ k : Perm (Fin n)) = σ := congrArg Subtype.val hk
    let u' : ↥⁅V₀, K⁆ := ⟨(k : X) * u * (k : X)⁻¹, conj_mem_commutator V₀ K hS.norm k k.2 u.2⟩
    refine (hmem _).2 ⟨u', Multiplicative.toAdd.injective ?_⟩
    have h1 := hπi k u u' rfl x (by rw [hu]; rfl)
    rw [hk2] at h1
    rw [h1]; rfl
  rcases altHeart_irreducible (by omega) S hinv with h | h
  · exfalso
    apply hne
    have h1 : ∀ u, π u = 1 := fun u => by
      have : Multiplicative.toAdd (π u) ∈ S := (hmem _).2 ⟨u, rfl⟩
      rw [h, AddSubgroup.mem_bot] at this
      exact Multiplicative.toAdd.injective (this.trans toAdd_one.symm)
    have h2 : ⁅⁅V₀, K⁆, K⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu k hk
      rw [Subgroup.mem_bot]
      have := hπk ⟨u, hu⟩ (h1 _) k hk
      exact commutatorElement_eq_one_iff_mul_comm.2 (by
        have := (mul_inv_eq_iff_eq_mul.1 this)
        exact this.symm)
    have h3 := altBaum_commutator_le_commutator_commutator hS.comm hS.norm Φ hS.surj h5 hS.ker
    rw [h2] at h3
    exact le_bot_iff.1 h3
  · intro v
    have : Multiplicative.toAdd v ∈ S := by rw [h]; trivial
    obtain ⟨u, hu⟩ := (hmem _).1 this
    exact ⟨u, by simpa using hu⟩

end Section

section Block

variable {H Kb U : Subgroup X}

theorem commutator_gnV_le_of_isBlock2 (hX : GNSetting X T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hblk : IsBlock2 H Kb) (hC : ¬ Kb ≤ gnC T)
    (hUV : U ≤ gnV T) (hUKb : ∀ k ∈ Kb, ∀ u ∈ U, k * u * k⁻¹ ∈ U) (hnt : ⁅U, Kb⁆ ≠ ⊥) :
    ⁅gnV T, Kb⁆ ≤ U := by
  have hshort := hblk.1
  have hodd := le_closure_odd_of_isShort2 hshort
  have hVU : ⁅gnV T, Kb⁆ = blockU Kb := commutator_gnV_eq_blockU_q hX hQH hblk hC
  have := normal_gnV (X := X) T
  have hU2 : IsPGroup 2 U :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).to_le
      (hUV.trans (gnV_le_pCoreOf hX))
  have hKbU : Kb ≤ Subgroup.normalizer (U : Set X) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hUKb k hk h, fun hh => ?_⟩
    have := hUKb k⁻¹ (Kb.inv_mem hk) _ hh
    simpa [mul_assoc] using this
  have hUinV : ⁅U, Kb⁆ ≤ ⁅gnV T, Kb⁆ := Subgroup.commutator_mono hUV le_rfl
  have hUinU : ⁅U, Kb⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.1 hKbU
  obtain ⟨-, hirr⟩ := hshort.2.2.2.2
  have hKbN_blockU : Kb ≤ Subgroup.normalizer (blockU Kb : Set X) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hKbN_S : Kb ≤ Subgroup.normalizer ((blockU Kb ⊓ U : Subgroup X) : Set X) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKbN_blockU hg, hKbU hg⟩
  have hZc : blockZ Kb ≤ Subgroup.centralizer (Kb : Set X) := inf_le_right
  have hKbN_Z : Kb ≤ Subgroup.normalizer (blockZ Kb : Set X) :=
    (Subgroup.le_centralizer_iff.1 hZc).trans (Subgroup.centralizer_le_normalizer _)
  rcases hirr (blockU Kb ⊓ U ⊔ blockZ Kb) le_sup_right (sup_le inf_le_left inf_le_left)
      (fun y hy => mem_normalizer_sup (hKbN_S hy) (hKbN_Z hy)) with h | h
  ·
    exfalso
    apply hnt
    have hSZ : blockU Kb ⊓ U ≤ blockZ Kb := le_sup_left.trans h.le
    have h1 : ⁅U, Kb⁆ ≤ blockU Kb ⊓ U := le_inf (hUinV.trans hVU.le) hUinU
    have h2 : ⁅⁅U, Kb⁆, Kb⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (h1.trans (hSZ.trans hZc))
    have h3 := commutator_le_commutator_commutator_of_odd hU2 hKbU hodd
    rw [h2] at h3
    exact le_bot_iff.1 h3
  ·
    rw [hVU]
    have hQ2 : IsPGroup 2 (pCoreOf 2 Kb) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Kb
    have h1 : blockU Kb ≤ ⁅blockU Kb, Kb⁆ :=
      commutator_le_commutator_commutator_of_odd hQ2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Kb) hodd
    have hVc := (isElemAbelian_gnV T hX).1
    have hZS : blockZ Kb ≤ Subgroup.centralizer ((blockU Kb ⊓ U : Subgroup X) : Set X) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hzV : z ∈ gnV T := blockU_le_gnV_q hX hQH hblk hC ((inf_le_left : blockZ Kb ≤ blockU Kb) hz)
      have hsV : s ∈ gnV T := blockU_le_gnV_q hX hQH hblk hC hs.1
      exact congrArg Subtype.val (hVc.is_comm.comm (⟨s, hsV⟩ : ↥(gnV T)) ⟨z, hzV⟩)
    have hZN : blockZ Kb ≤ Subgroup.normalizer ((blockU Kb ⊓ U : Subgroup X) : Set X) := fun z hz =>
      (Subgroup.centralizer_le_normalizer _) (hZS hz)
    have hmulset := Subgroup.coe_mul_of_right_le_normalizer_left (blockU Kb ⊓ U) (blockZ Kb) hZN
    have h2 : ⁅blockU Kb, Kb⁆ ≤ blockU Kb ⊓ U := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have hu' : u ∈ ((blockU Kb ⊓ U ⊔ blockZ Kb : Subgroup X) : Set X) := by rw [h]; exact hu
      rw [hmulset] at hu'
      obtain ⟨s, hs, z, hz, rfl⟩ := hu'
      have hzk : k * z = z * k := ((Subgroup.mem_centralizer_iff.1 (hZc hz)) k hk)
      have hzk' : z * k * z⁻¹ = k := by rw [mul_inv_eq_iff_eq_mul]; exact hzk.symm
      have e : ⁅s * z, k⁆ = s * (k * s⁻¹ * k⁻¹) := by
        calc ⁅s * z, k⁆ = s * (z * k * z⁻¹) * s⁻¹ * k⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = s * (k * s⁻¹ * k⁻¹) := by rw [hzk']; group
      rw [e]
      exact (blockU Kb ⊓ U).mul_mem hs
        ((Subgroup.mem_normalizer_iff.1 (hKbN_S hk) s⁻¹).1 ((blockU Kb ⊓ U).inv_mem hs))
    exact h1.trans (h2.trans inf_le_right)

end Block

section Whole

variable {K H Kb U : Subgroup X} {n : ℕ} {Φ : ↥K →* alternatingGroup (Fin n)}

theorem commutator_gnV_le_of_block (hX : GNSetting X T) (h5 : 5 ≤ n) (hCK : gnC T ≤ K)
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T)
    (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hblk : IsBlock2 H Kb) (hC : ¬ Kb ≤ gnC T)
    (hKb : Kb ≤ K) (hUV : U ≤ gnV T) (hUK : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U)
    (hnt : ⁅U, Kb⁆ ≠ ⊥) : ⁅gnV T, K⁆ ≤ U := by
  have := normal_gnV (X := X) T
  have hKbV := commutator_gnV_le_of_isBlock2 hX hQH hblk hC hUV
    (fun k hk u hu => hUK k (hKb hk) u hu) hnt
  let Ker : Subgroup X :=
    { carrier := {k | k ∈ K ∧ ∀ v ∈ gnV T, ⁅v, k⁆ ∈ U}
      one_mem' := ⟨K.one_mem, fun v _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨K.mul_mem haK hbK, fun v hv => ?_⟩
        have e : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]; exact U.mul_mem (ha v hv) (hUK a haK _ (hb v hv))
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨K.inv_mem haK, fun v hv => ?_⟩
        have e : ⁅v, a⁻¹⁆ = a⁻¹ * ⁅v, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        simpa using hUK a⁻¹ (K.inv_mem haK) _ (U.inv_mem (ha v hv)) }
  have hKerK : Ker ≤ K := fun k hk => hk.1
  have hKb_Ker : Kb ≤ Ker := fun k hk =>
    ⟨hKb hk, fun v hv => hKbV (Subgroup.commutator_mem_commutator hv hk)⟩
  have hC_Ker : gnC T ≤ Ker := fun c hc => ⟨hCK hc, fun v hv => by
    have : ⁅v, c⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hc v hv)
    rw [this]; exact U.one_mem⟩
  have hKerN : (Ker.subgroupOf K).Normal :=
    normal_subgroupOf_of_forall_conj_mem hKerK fun k hk y hy =>
      ⟨K.mul_mem (K.mul_mem hk (hKerK hy)) (K.inv_mem hk), fun v hv => by
        have e : ⁅v, k * y * k⁻¹⁆ = k * ⁅k⁻¹ * v * k, y⁆ * k⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hUK k hk _ (hy.2 _ (‹(gnV T).Normal›.conj_mem v hv k⁻¹ |> fun h => by
          simpa [mul_assoc] using h))⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact h5)
  have hNimg : ((Ker.subgroupOf K).map Φ).Normal := hKerN.map Φ hΦs
  have hne : (Ker.subgroupOf K).map Φ ≠ ⊥ := by
    intro h
    apply hC
    intro k hk
    have : Φ ⟨k, hKb hk⟩ ∈ (Ker.subgroupOf K).map Φ := Subgroup.mem_map_of_mem Φ (hKb_Ker hk)
    rw [h, Subgroup.mem_bot] at this
    exact (hΦk _).1 this
  have htop : (Ker.subgroupOf K).map Φ = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hNimg).resolve_left hne
  have hKK : K ≤ Ker := by
    intro k hk
    have : Φ ⟨k, hk⟩ ∈ (Ker.subgroupOf K).map Φ := by rw [htop]; trivial
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 this
    have hy1 : Φ (y⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hyk, inv_mul_cancel]
    have hc : ((y⁻¹ * ⟨k, hk⟩ : ↥K) : X) ∈ Ker := hC_Ker ((hΦk _).1 hy1)
    have hk' : k = (y : X) * ((y⁻¹ * ⟨k, hk⟩ : ↥K) : X) := by simp
    rw [hk']
    exact Ker.mul_mem hy hc
  rw [Subgroup.commutator_le]
  intro v hv k hk
  exact (hKK hk).2 v hv

end Whole

section Final

theorem false_of_block_of_naturalOn (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n)
    (g : ↥L →* alternatingGroup (Fin n)) (hg : Function.Surjective g)
    (W : Subgroup X) (hWV : W ≤ gnV T)
    (hWK : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart n))
    (hπk : ∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
      (k : X) * u * (k : X)⁻¹ = u)
    (hπi : ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n))
    (hWne : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≠ ⊥)
    {H Kb : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hblk : IsBlock2 H Kb)
    (hC : ¬ Kb ≤ gnC T) (hKL : gnImg T Kb ≤ L) : False := by
  have hgi : Function.Injective g := injective_of_surjective_component hX hL (by omega) hg
  have hΦs : Function.Surjective (liftToAlt L g) := liftToAlt_surjective L hg
  have hΦk := liftToAlt_eq_one_iff L hgi
  have hCK : gnC T ≤ L.comap (QuotientGroup.mk' (gnC T)) := fun c hc => by
    show QuotientGroup.mk' (gnC T) c ∈ L
    rw [show QuotientGroup.mk' (gnC T) c = 1 from (QuotientGroup.eq_one_iff c).2 hc]
    exact L.one_mem
  have hKb : Kb ≤ L.comap (QuotientGroup.mk' (gnC T)) := fun x hx =>
    hKL (Subgroup.mem_map_of_mem _ hx)
  have hVel : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  have := normal_gnV (X := X) T
  have hVC : ∀ c ∈ gnC T, ∀ v ∈ gnV T, c * v * c⁻¹ = v := fun c hc v hv => by
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.1 hc v hv
    rw [← h1, mul_inv_cancel_right]
  have hSW : AltBaumSetup W (L.comap (QuotientGroup.mk' (gnC T))) (liftToAlt L g) :=
    { comm := fun v hv w hw =>
        congrArg Subtype.val (hVel.1.is_comm.comm ⟨v, hWV hv⟩ ⟨w, hWV hw⟩)
      sq := fun v hv => by have := hVel.2 v (hWV hv); simpa [pow_two] using this
      norm := hWK
      surj := hΦs
      ker := fun k hk v hv => hVC _ ((hΦk k).1 hk) v (hWV hv) }
  have hπi' : ∀ (l : ↥(L.comap (QuotientGroup.mk' (gnC T)))) (u u' : ↥⁅W, L.comap
      (QuotientGroup.mk' (gnC T))⁆), (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
      Multiplicative.toAdd (π u') = (QuotientAddGroup.mk
        (evenWeightPerm (liftToAlt L g l : Perm (Fin n)) x) : altHeart n) :=
    fun l u u' h x hx => hπi (l : X) l.2 u u' h x hx
  have hπs : Function.Surjective π := surjective_of_ne_bot (by omega) hSW hπk hπi' hWne
  obtain ⟨π', hπ'⟩ := exists_altBaumSection_of_setup hn9 hodd hSW hπs hπk hπi'
  have hnt : ⁅⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆, Kb⁆ ≠ ⊥ := by
    intro hbot
    apply hC
    intro k hk
    have hfix : ∀ v : evenWeight n,
        evenWeightPerm (liftToAlt L g ⟨k, hKb hk⟩ : Perm (Fin n)) v = v := by
      intro v
      obtain ⟨u, hu⟩ := hπ'.surj (Multiplicative.ofAdd v)
      have hcomm : (k : X) * u * (k : X)⁻¹ = u := by
        have h1 : ⁅(u : X), k⁆ ∈ ⁅⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆, Kb⁆ :=
          Subgroup.commutator_mem_commutator u.2 hk
        rw [hbot, Subgroup.mem_bot] at h1
        rw [mul_inv_eq_iff_eq_mul]
        exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
      have h2 := hπ'.equivar ⟨k, hKb hk⟩ u u hcomm.symm
      rw [hu] at h2
      exact h2.symm
    have := eq_one_of_evenWeightPerm_eq_self hodd hfix
    exact (hΦk _).1 (Subtype.ext this)
  have hWU : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ gnV T :=
    (commutator_le_of_invariant W _ hWK).trans hWV
  have hle : ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤
      ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ :=
    commutator_gnV_le_of_block hX (by omega) hCK hΦs hΦk hQH hblk hC hKb hWU
      (fun k hk u hu => conj_mem_commutator W _ hWK k hk hu) hnt
  have hge : ⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ ≤
      ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ := Subgroup.commutator_mono hWV le_rfl
  let πV : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (evenWeight n) :=
    π'.comp (Subgroup.inclusion hle)
  have hSV := altBaumSetup_gnV hX hΦs hΦk
  have hπV : AltBaumSection (gnV T) (L.comap (QuotientGroup.mk' (gnC T))) (liftToAlt L g) πV :=
    { surj := fun v => by
        obtain ⟨u, hu⟩ := hπ'.surj v
        exact ⟨⟨u.1, hge u.2⟩, hu⟩
      ker_iff := fun u => hπ'.ker_iff (Subgroup.inclusion hle u)
      equivar := fun l u u' h => hπ'.equivar l (Subgroup.inclusion hle u)
        (Subgroup.inclusion hle u') h }
  exact false_of_block_of_altBaumSection hX hL hn9 hodd hΦs hΦk hSV hπV hQH hblk hC hKL

end Final

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
