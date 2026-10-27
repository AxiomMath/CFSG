module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Layer
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.CatUnitarySix
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Rank
public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LieType.SeitzGeneration CFSG.Open

theorem catTwistedAFive_center_eq_bot {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) :
    Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) = ⊥ := by
  obtain ⟨hs, a, b, hab⟩ := isSimpleGroup_cat_twistedA_five hv
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩)) with h | h
  · exact h
  · exfalso
    have : b ∈ Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 this a)

theorem layer_le_hyperClosure_of_plane
    {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hpq : p ∣ q.card ^ 2 - q.card + 1)
    (E : Subgroup G) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    {y : G} (hyE : y ∈ E) (hy1 : y ≠ 1) (L : Subgroup G)
    (hLy : ∀ l ∈ L, l * y = y * l)
    (ρ : L →* Cat ⟨.twistedA 5 q, hv⟩) (hρ : Function.Surjective ρ)
    (β : E →* Cat ⟨.twistedA 5 q, hv⟩) (hβy : β ⟨y, hyE⟩ = 1) (hβcard : Nat.card β.range = p ^ 2)
    (hcomm : ∀ (e : E) (l : L), ρ l * β e = β e * ρ l → (l : G) * e = e * (l : G)) :
    L ≤ hyperClosure p (⊤ : Subgroup G) E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨hn0, -, -⟩ := not_dvd_of_dvd_phiSix hp hp3 hpq
  have hp2 := ne_two_of_dvd_phiSix hpq
  set hc : Subgroup G := hyperClosure p (⊤ : Subgroup G) E with hhc
  have key : ∀ (l : L) (e : E), β e ≠ 1 → (l : G) * e = e * (l : G) → (l : G) ∈ hc := by
    intro l e he1 hle
    refine mem_hyperClosure_of_dvd_card hp hEcard ?_
    refine sq_dvd_card_inf_centralizer hp hE e.2 hyE ?_ hle.symm (hLy l l.2).symm ?_
    · intro h
      exact he1 (by rw [show e = 1 from Subtype.ext h, map_one])
    · intro hyz
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hyz
      have hβe : β ⟨y, hyE⟩ = β e ^ m := by
        have : (⟨y, hyE⟩ : E) = e ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
        rw [this, map_zpow]
      rw [hβy] at hβe
      have hord : orderOf (β e) = p := by
        refine orderOf_eq_prime ?_ he1
        rw [← map_pow]
        have : e ^ p = 1 := Subtype.ext (hE.2 e e.2)
        rw [this, map_one]
      have hdvd : (p : ℤ) ∣ m := by
        rw [← hord]
        exact orderOf_dvd_iff_zpow_eq_one.2 hβe.symm
      obtain ⟨k, hk⟩ := hdvd
      apply hy1
      rw [← hm, hk, zpow_mul]
      have : e.1 ^ (p : ℤ) = 1 := by simpa using hE.2 e e.2
      rw [this, one_zpow]
  have hker : ∀ z : L, z ∈ ρ.ker → (z : G) ∈ hc := by
    intro z hz
    refine mem_hyperClosure_of_dvd_card hp hEcard ?_
    have hle : E ≤ Subgroup.centralizer {(z : G)} := fun e he m hm => by
      rw [Set.mem_singleton_iff.1 hm]
      have h1 : ρ z * β ⟨e, he⟩ = β ⟨e, he⟩ * ρ z := by rw [MonoidHom.mem_ker.1 hz, one_mul, mul_one]
      exact hcomm ⟨e, he⟩ z h1
    rw [inf_eq_left.2 hle, hEcard]
    exact pow_dvd_pow p (by norm_num)
  have hcenter := catTwistedAFive_center_eq_bot hv
  have hconjinj : Function.Injective
      (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →* MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have : a ∈ Subgroup.center (Cat ⟨.twistedA 5 q, hv⟩) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun m : MulAut _ => m g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rwa [hcenter, Subgroup.mem_bot] at this
  let φ : E →* MulAut (Cat ⟨.twistedA 5 q, hv⟩) :=
    (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →* MulAut (Cat ⟨.twistedA 5 q, hv⟩)).comp β
  have hφinj : ∀ a, φ a = 1 → β a = 1 := fun a ha => hconjinj (by simpa [φ] using ha)
  let E' : Subgroup (MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := φ.range
  have hE'card : Nat.card E' = p ^ 2 := by
    have : E' = β.range.map (MulAut.conj : Cat ⟨.twistedA 5 q, hv⟩ →*
        MulAut (Cat ⟨.twistedA 5 q, hv⟩)) := MonoidHom.range_comp _ _
    rw [this, Subgroup.card_map_of_injective hconjinj, hβcard]
  have hE'el : IsElemAbelian p E' := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨a, ha⟩ := u.2
      obtain ⟨b, hb⟩ := v.2
      apply Subtype.ext
      show (u : MulAut (Cat ⟨.twistedA 5 q, hv⟩)) * v = v * u
      rw [← ha, ← hb, ← map_mul, ← map_mul, hE.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hE.2 a a.2)
      rw [this, map_one]
  have hinner : E' ≤ (MulAut.conj :
      Cat ⟨.twistedA 5 q, hv⟩ →* MulAut (Cat ⟨.twistedA 5 q, hv⟩)).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨β a, rfl⟩
  have hpd : p ≠ (⟨.twistedA 5 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := by
    intro h
    have h' : p = q.p := by simpa using h
    apply hn0
    rw [h']
    have : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact Dvd.dvd.pow this two_ne_zero
  have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p (TauCeti.LieTypeIndex.twistedA 5 q) := by
    rintro (⟨h3, _⟩ | ⟨_, h | h⟩)
    · exact hp3 h3
    · cases h
    · cases h
  have hgen : PlaneGen E' :=
    seitzInnerLowClassical_of_heisCore unitaryHeisCore ⟨.twistedA 5 q, hv⟩ p hp hp2 hpd hex E'
      hE'el hE'card ⟨hinner, rankLE2_cat_twistedA_five hv hp hp3 hpq, by
        unfold IsClassicalIndex; trivial⟩
  set M : Subgroup L := hc.comap L.subtype with hM
  have hMmap : M.map ρ = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨ε, ⟨a, rfl⟩, hε1, hεk⟩
    obtain ⟨l, rfl⟩ := hρ k
    have ha1 : β a ≠ 1 := fun h => hε1 (by simp [φ, h])
    have h : β a * ρ l * (β a)⁻¹ = ρ l := hεk
    have hl : l ∈ M := key l a ha1 (hcomm a l (by
      have h' := mul_inv_eq_iff_eq_mul.1 h
      exact h'.symm))
    exact ⟨l, hl, rfl⟩
  intro l hl
  have hmem : ρ ⟨l, hl⟩ ∈ M.map ρ := by rw [hMmap]; exact Subgroup.mem_top _
  obtain ⟨m, hm, hml⟩ := Subgroup.mem_map.1 hmem
  have hz : m⁻¹ * ⟨l, hl⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hml, inv_mul_cancel]
  have hzc : ((m⁻¹ * ⟨l, hl⟩ : L) : G) ∈ hc := hker _ hz
  have hlm : l = (m : G) * ((m⁻¹ * ⟨l, hl⟩ : L) : G) := by simp
  rw [hlm]
  exact hc.mul_mem (Subgroup.mem_comap.1 hm) hzc

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
