module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Pull
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}
  {EY : Subgroup (MulAut (↥L ⧸ center ↥L))} (h : PullHyp G L z t T EY)

namespace PullHyp

@[reducible] noncomputable def S (h : PullHyp G L z t T EY) : Subgroup (MulAut (↥L ⧸ center ↥L)) :=
  (T.subgroupOf (centralizer ({z} : Set G))).map (thetaH h.cfg.cent_le)

include h in
theorem EY_normal {σ : MulAut (↥L ⧸ center ↥L)} (hσ : σ ∈ h.S) {ε : MulAut (↥L ⧸ center ↥L)}
    (hε : ε ∈ EY) : σ * ε * σ⁻¹ ∈ EY := by
  have hPS : EY.map (MulAut.conj σ).toMonoidHom ≤ h.S := by
    rintro _ ⟨ε', hε', rfl⟩
    have h1 := h.facts.E_le hε'
    simpa [MulAut.conj_apply] using mul_mem (mul_mem hσ h1) (inv_mem hσ)
  have hiso : Nonempty (↥EY ≃* ↥(EY.map (MulAut.conj σ).toMonoidHom)) :=
    ⟨EY.equivMapOfInjective _ (MulAut.conj σ).injective⟩
  have heq := h.facts.unique _ hPS hiso
  rw [← heq]
  exact ⟨ε, hε, by simp [MulAut.conj_apply]⟩

include h in
theorem map_nuL_comap : (EY.comap (nuL L)).map (nuL L) = EY :=
  Subgroup.map_comap_eq_self (fun ε hε => by
    obtain ⟨l, hl⟩ := h.exists_nuL_of_mem hε
    exact ⟨l, hl⟩)

include h in
theorem equiv_EY_pullE : Nonempty (↥EY ≃* ↥(pullE L EY)) := by
  obtain ⟨e1⟩ := equivMap_of_ker (nuL L) (EY.comap (nuL L)) (fun _ _ hx => h.nuL_inj
    (hx.trans (map_one _).symm))
  have e2 : ↥(EY.comap (nuL L)) ≃* ↥(pullE L EY) :=
    (EY.comap (nuL L)).equivMapOfInjective L.subtype L.subtype_injective
  have e3 : ↥(EY.comap (nuL L)) ≃* ↥EY :=
    e1.trans (MulEquiv.subgroupCongr h.map_nuL_comap)
  exact ⟨e3.symm.trans e2⟩

include h in
theorem equiv_image {P : Subgroup G} (hP : P ≤ T) (hz : z ∉ P) :
    Nonempty (↥P ≃* ↥((P.subgroupOf (centralizer ({z} : Set G))).map
      (thetaH h.cfg.cent_le))) := by
  have hPH : P ≤ centralizer ({z} : Set G) := fun p hp => h.cfg.T_le (hP hp)
  have hker : ∀ x ∈ P.subgroupOf (centralizer ({z} : Set G)), thetaH h.cfg.cent_le x = 1 →
      x = 1 := by
    intro x hx hx1
    have hxz : (x : G) ∈ zpowers z := (h.ker x).1 hx1
    have hxP : (x : G) ∈ P := mem_subgroupOf.1 hx
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hxz with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      rw [h1] at hxP
      exact hz hxP
  obtain ⟨φ1⟩ := equivMap_of_ker (thetaH h.cfg.cent_le) _ hker
  exact ⟨(subgroupOfEquivOfLe hPH).symm.trans φ1⟩

include h in
theorem image_le {P : Subgroup G} (hP : P ≤ T) :
    (P.subgroupOf (centralizer ({z} : Set G))).map (thetaH h.cfg.cent_le) ≤ h.S :=
  Subgroup.map_mono (fun _ hx => mem_subgroupOf.2 (hP (mem_subgroupOf.1 hx)))

include h in
theorem U {P : Subgroup G} (hP : P ≤ T) (hz : z ∉ P)
    (hiso : Nonempty (↥(pullE L EY) ≃* ↥P)) : P ≤ pullE L EY ⊔ zpowers z := by
  obtain ⟨ψ⟩ := hiso
  obtain ⟨e1⟩ := h.equiv_EY_pullE
  obtain ⟨e2⟩ := h.equiv_image hP hz
  have hEq := h.facts.unique _ (h.image_le hP) ⟨e1.trans (ψ.trans e2)⟩
  intro p hp
  have hpH : p ∈ centralizer ({z} : Set G) := h.cfg.T_le (hP hp)
  have hmem : h.th p hpH ∈ EY := by
    have hmem' : h.th p hpH ∈ (P.subgroupOf (centralizer ({z} : Set G))).map
        (thetaH h.cfg.cent_le) := ⟨⟨p, hpH⟩, mem_subgroupOf.2 hp, rfl⟩
    rw [hEq] at hmem'
    exact hmem'
  obtain ⟨l, hl, hll, hlν⟩ := h.exists_mem_pullE hmem
  have h1 : h.th l (h.L_le_H hll) = h.th p hpH := by
    rw [h.th_L hll]; exact hlν
  have h2 := (h.th_eq_iff _ _).1 h1
  have : p = l * (l⁻¹ * p) := by group
  rw [this]
  exact mul_mem_sup hl h2

include h in
theorem C {s : G} (hs : s ∈ T) (hc : ∀ e ∈ pullE L EY, s * e = e * s) :
    s = 1 ∨ s = z ∨ s = t ∨ s = z * t := by
  have hsH : s ∈ centralizer ({z} : Set G) := h.cfg.T_le hs
  have hcent : ∀ ε ∈ EY, h.th s hsH * ε = ε * h.th s hsH := by
    intro ε hε
    obtain ⟨e, he, hel, hεe⟩ := h.exists_mem_pullE hε
    have h1 : h.th s hsH * h.th e (h.L_le_H hel) = h.th e (h.L_le_H hel) * h.th s hsH := by
      rw [← h.th_mul, ← h.th_mul]
      congr 1
      exact hc e he
    rw [h.th_L hel, hεe] at h1
    exact h1
  have htL : h.th t (h.L_le_H h.cfg.t_mem_A) = MulAut.conj ((⟨t, h.cfg.t_mem_A⟩ : ↥L) :
      ↥L ⧸ center ↥L) := h.th_L h.cfg.t_mem_A
  have htH : t ∈ centralizer ({z} : Set G) := h.L_le_H h.cfg.t_mem_A
  rcases h.facts.cent _ (h.th_mem_S hs) hcent with h1 | h1
  · have h2 := (h.th_eq_one_iff hsH).1 h1
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
  · have h1' : h.th s hsH = h.th t htH := by rw [h1]; exact htL.symm
    have h2 := (h.th_eq_iff hsH htH).1 h1'
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq h2 with h3 | h3
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact (inv_mul_eq_one.1 h3)
    · refine Or.inr (Or.inr (Or.inr ?_))
      calc s = t * (s⁻¹ * t)⁻¹ := by group
        _ = t * z⁻¹ := by rw [h3]
        _ = t * z := by rw [inv_eq_of_mul_eq_one_right h.cfg.z_sq]
        _ = z * t := h.cfg.t_comm_z


include h in
theorem econfig [Finite G] : EConfig L (T ⊓ L) (pullE L EY) t := by
  have hinj := h.nuL_inj
  refine
  { le := fun e he => ⟨h.pullE_le_T he, pullE_le_L L EY he⟩
    t_mem := h.t_mem_pullE
    conj := ?_
    gen := ?_
    nonab := ?_
    comm := ?_
    center := ?_
    unique := ?_
    normal := ?_
    cent := ?_ }
  · intro e he he2 he1
    obtain ⟨hl, hν⟩ := mem_pullE.1 he
    have hsq : nuL L ⟨e, hl⟩ * nuL L ⟨e, hl⟩ = 1 := by
      rw [← map_mul]
      have : (⟨e, hl⟩ : ↥L) * ⟨e, hl⟩ = 1 := Subtype.ext he2
      rw [this, map_one]
    have hne : nuL L ⟨e, hl⟩ ≠ 1 := fun h' => he1 (by
      have := hinj (h'.trans (map_one _).symm)
      exact congrArg Subtype.val this)
    obtain ⟨c, hc⟩ := h.facts.E_conj _ hν hsq hne
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨c', c'.2, ?_⟩
    have hc' : nuL L ⟨e, hl⟩ = nuL L (c' * ⟨t, h.cfg.t_mem_A⟩ * c'⁻¹) := by
      rw [hc]
      simp only [nuL_apply, map_mul, map_inv]
    exact congrArg Subtype.val (hinj hc')
  · set EL : Subgroup ↥L := EY.comap (nuL L) with hEL
    set XL : Set ↥L := {l | l ∈ EL ∧ l * l = 1 ∧ l ≠ 1} with hXL
    have hX : nuL L '' XL = {ε | ε ∈ EY ∧ ε * ε = 1 ∧ ε ≠ 1} := by
      ext ε
      constructor
      · rintro ⟨l, ⟨hlE, hl2, hl1⟩, rfl⟩
        refine ⟨hlE, ?_, ?_⟩
        · rw [← map_mul, hl2, map_one]
        · intro h'
          exact hl1 (hinj (h'.trans (map_one _).symm))
      · rintro ⟨hε, hε2, hε1⟩
        obtain ⟨l, hl⟩ := h.exists_nuL_of_mem hε
        refine ⟨l, ⟨by rw [hEL, mem_comap, hl]; exact hε, ?_, ?_⟩, hl⟩
        · apply hinj
          rw [map_mul, hl, hε2, map_one]
        · intro h'
          apply hε1
          rw [← hl, h', map_one]
    have h1 : (closure XL).map (nuL L) = EY := by
      rw [MonoidHom.map_closure, hX, ← h.facts.E_gen]
    have hEL' : EL = closure XL := by
      have := congrArg (Subgroup.comap (nuL L)) h1
      rw [Subgroup.comap_map_eq_self_of_injective hinj] at this
      exact this.symm
    have h2 : pullE L EY = (closure XL).map L.subtype := by rw [← hEL']; rfl
    have h3 : (closure XL).map L.subtype = closure (L.subtype '' XL) :=
      MonoidHom.map_closure _ _
    have h4 : L.subtype '' XL = {e | e ∈ pullE L EY ∧ e * e = 1 ∧ e ≠ 1} := by
      ext e
      constructor
      · rintro ⟨l, ⟨hlE, hl2, hl1⟩, rfl⟩
        refine ⟨mem_pullE.2 ⟨l.2, hlE⟩, congrArg Subtype.val hl2, fun h' => hl1 (Subtype.ext h')⟩
      · rintro ⟨he, he2, he1⟩
        obtain ⟨hl, hν⟩ := mem_pullE.1 he
        exact ⟨⟨e, hl⟩, ⟨hν, Subtype.ext he2, fun h' => he1 (congrArg Subtype.val h')⟩, rfl⟩
    calc pullE L EY = (closure XL).map L.subtype := h2
      _ = closure (L.subtype '' XL) := h3
      _ = closure {e | e ∈ pullE L EY ∧ e * e = 1 ∧ e ≠ 1} := by rw [h4]
  · obtain ⟨ε₁, h₁, ε₂, h₂, hne⟩ := h.facts.E_nonab
    obtain ⟨e₁, he₁, hl₁, hνe₁⟩ := h.exists_mem_pullE h₁
    obtain ⟨e₂, he₂, hl₂, hνe₂⟩ := h.exists_mem_pullE h₂
    refine ⟨e₁, he₁, e₂, he₂, fun h' => hne ?_⟩
    rw [← hνe₁, ← hνe₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h'
  · intro e₁ he₁ e₂ he₂
    obtain ⟨hl₁, hν₁⟩ := mem_pullE.1 he₁
    obtain ⟨hl₂, hν₂⟩ := mem_pullE.1 he₂
    have hcomm : nuL L ⟨e₁, hl₁⟩ * nuL L ⟨e₂, hl₂⟩ * (nuL L ⟨e₁, hl₁⟩)⁻¹ *
        (nuL L ⟨e₂, hl₂⟩)⁻¹ = nuL L (⟨e₁, hl₁⟩ * ⟨e₂, hl₂⟩ * ⟨e₁, hl₁⟩⁻¹ * ⟨e₂, hl₂⟩⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rcases h.facts.E_comm _ hν₁ _ hν₂ with h' | h'
    · left
      rw [hcomm] at h'
      exact congrArg Subtype.val (hinj (h'.trans (map_one _).symm))
    · right
      rw [hcomm] at h'
      exact congrArg Subtype.val (hinj h')
  · intro y hy hc
    obtain ⟨hl, hν⟩ := mem_pullE.1 hy
    have key := h.facts.E_center _ hν (fun f hf => by
      obtain ⟨e, he, hle, hfe⟩ := h.exists_mem_pullE hf
      rw [← hfe, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc e he))
    rcases key with h1 | h1
    · left
      exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
    · right
      exact congrArg Subtype.val (hinj h1)
  · intro P hP hiso
    obtain ⟨ψ⟩ := hiso
    have hz : z ∉ P := fun hzP => h.cfg.z_not_mem_A (hP hzP).2
    have hP' : P ≤ T := fun p hp => (hP hp).1
    obtain ⟨e1⟩ := h.equiv_EY_pullE
    obtain ⟨e2⟩ := h.equiv_image hP' hz
    have hEq := h.facts.unique _ (h.image_le hP') ⟨e1.trans (ψ.trans e2)⟩
    have hPE : P ≤ pullE L EY := by
      intro p hp
      have hpL : p ∈ L := (hP hp).2
      have hpH : p ∈ centralizer ({z} : Set G) := h.L_le_H hpL
      have hmem' : h.th p hpH ∈ (P.subgroupOf (centralizer ({z} : Set G))).map
          (thetaH h.cfg.cent_le) := ⟨⟨p, hpH⟩, mem_subgroupOf.2 hp, rfl⟩
      rw [hEq] at hmem'
      rw [h.th_L hpL] at hmem'
      exact mem_pullE.2 ⟨hpL, hmem'⟩
    exact Subgroup.eq_of_le_of_card_ge hPE (Nat.card_congr ψ.toEquiv).le
  · intro s hs e he
    obtain ⟨hel, hν⟩ := mem_pullE.1 he
    have hsν := h.nuL_mem_S hs
    have h1 := h.EY_normal hsν hν
    have hsl : s * e * s⁻¹ ∈ L := mul_mem (mul_mem hs.2 hel) (inv_mem hs.2)
    refine mem_pullE.2 ⟨hsl, ?_⟩
    have : nuL L ⟨s * e * s⁻¹, hsl⟩ = nuL L ⟨s, hs.2⟩ * nuL L ⟨e, hel⟩ * (nuL L ⟨s, hs.2⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact h1
  · intro s hs hc
    have hsν := h.nuL_mem_S hs
    have key := h.facts.cent _ hsν (fun ε hε => by
      obtain ⟨e, he, hel, hεe⟩ := h.exists_mem_pullE hε
      rw [← hεe, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc e he))
    rcases key with h1 | h1
    · left
      exact congrArg Subtype.val (hinj (h1.trans (map_one _).symm))
    · right
      exact congrArg Subtype.val (hinj h1)

include h in
theorem outerE [Finite G] : OuterE G L z t T (pullE L EY) where
  cfg := h.cfg
  econfig := h.econfig
  U := fun _ hP hz hiso => h.U hP hz hiso
  C := fun _ hs hc => h.C hs hc

end PullHyp

end CFSG.EvenSporadicStandard.Fin76b
