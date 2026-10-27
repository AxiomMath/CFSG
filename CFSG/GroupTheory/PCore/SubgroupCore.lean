module

public import CFSG.Open.GLADefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG

open CFSG.Open
open scoped commutatorElement

theorem coprime_card_pPrimeCore (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Nat.Coprime p (Nat.card (pPrimeCore p G)) := by
  refine Nat.coprime_of_dvd fun q hq hqp => ?_
  haveI : Fact q.Prime := ⟨hq⟩
  have hle : pPrimeCore p G ≤ pPrimeCore q G :=
    sSup_le fun N hN =>
      le_sSup (show N ∈ {K : Subgroup G | K.Normal ∧ Nat.Coprime q (Nat.card K)} from
        ⟨hN.1, Nat.Coprime.coprime_dvd_left hqp hN.2⟩)
  intro hqd
  exact (hq.coprime_iff_not_dvd).1 (pPrimeCore_coprime_card (p := q) (G := G))
    (hqd.trans (Subgroup.card_dvd_of_le hle))

variable {G : Type*} [Group G]

theorem gLAPPrimeCoreOf_map_mulEquiv {G H : Type*} [Group G] [Group H] (p : ℕ) (e : G ≃* H)
    (K : Subgroup G) :
    GLAPPrimeCoreOf p (K.map (e : G →* H)) = (GLAPPrimeCoreOf p K).map (e : G →* H) := by
  have h : (pPrimeCore p ↥K).map (MulEquiv.subgroupMap e K).toMonoidHom =
      pPrimeCore p ↥(K.map (e : G →* H)) := pPrimeCore_map_iso p (MulEquiv.subgroupMap e K)
  change (pPrimeCore p ↥(K.map (e : G →* H))).map (K.map (e : G →* H)).subtype =
    ((pPrimeCore p ↥K).map K.subtype).map (e : G →* H)
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem gLAPPrimeCoreOf_normal (p : ℕ) (H : Subgroup G) :
    ((GLAPPrimeCoreOf p H).subgroupOf H).Normal := by
  have h : (GLAPPrimeCoreOf p H).subgroupOf H = pPrimeCore p ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h]
  infer_instance

theorem gLAPPrimeCoreOf_eq_self_of_coprime [Finite G] {p : ℕ} {H : Subgroup G}
    (h : Nat.Coprime p (Nat.card H)) : GLAPPrimeCoreOf p H = H := by
  have htop : GLAPPrimeCore p ↥H = ⊤ := by
    refine top_le_iff.1 (le_sSup ?_)
    exact ⟨inferInstance, by simpa using h⟩
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  intro x hx
  exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, by rw [htop]; exact Subgroup.mem_top _, rfl⟩

theorem gLAPPrimeCoreOf_le_of_normal [Finite G] {p : ℕ} {K H : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).Normal) : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p H := by
  have hNH : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).1 hK
  have hOH : GLAPPrimeCoreOf p K ≤ H := (Subgroup.map_subtype_le (pPrimeCore p ↥K)).trans hKH
  have hOM : H ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← gLAPPrimeCoreOf_map_mulEquiv,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hNH hm)]
  have hOn : ((GLAPPrimeCoreOf p K).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).2 hOM
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p K)) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact coprime_card_pPrimeCore p ↥K
  have hle : (GLAPPrimeCoreOf p K).subgroupOf H ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hOn, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
      exact hcop⟩
  calc GLAPPrimeCoreOf p K = ((GLAPPrimeCoreOf p K).subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hOH).symm
    _ ≤ (pPrimeCore p ↥H).map H.subtype := Subgroup.map_mono hle
    _ = GLAPPrimeCoreOf p H := rfl

theorem gLAPPrimeCoreOf_inf_centralizer_conj (p : ℕ) (I : Subgroup G) [I.Normal] (g x : G) :
    Nonempty (GLAPPrimeCoreOf p (I ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G)) ≃*
      GLAPPrimeCoreOf p (I ⊓ Subgroup.centralizer ({x} : Set G))) := by
  have hyx : g * x * g⁻¹ = (MulAut.conj g : G →* G) x := (MulAut.conj_apply g x).symm
  rw [hyx]
  have hcen : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g : G →* G) =
      Subgroup.centralizer ({(MulAut.conj g : G →* G) x} : Set G) := by
    refine le_antisymm ?_ ?_
    · have h := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
        (MulAut.conj g : G →* G)
      simpa [Set.image_singleton] using h
    · intro z hz
      refine Subgroup.mem_map.2 ⟨(MulAut.conj g).symm z, ?_, (MulAut.conj g).apply_symm_apply z⟩
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      refine (MulAut.conj g).injective ?_
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz _ (Set.mem_singleton _)
  have hI : I.map (MulAut.conj g : G →* G) = I := Subgroup.Normal.map_conj_eq (H := I) g
  have hK : (I ⊓ Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g : G →* G) =
      I ⊓ Subgroup.centralizer ({(MulAut.conj g : G →* G) x} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hI, hcen]
  have hcore := gLAPPrimeCoreOf_map_mulEquiv p (MulAut.conj g)
    (I ⊓ Subgroup.centralizer ({x} : Set G))
  rw [hK] at hcore
  rw [hcore]
  exact ⟨(MulEquiv.subgroupMap (MulAut.conj g) _).symm⟩

theorem odd_card_gLAPPrimeCoreOf_of_odd_relIndex [Finite G] {p : ℕ} {L X : Subgroup G}
    (hLX : L ≤ X) (hn : (L.subgroupOf X).Normal) (hi : Odd (L.relIndex X))
    (hL : Odd (Nat.card (GLAPPrimeCoreOf p L))) : Odd (Nat.card (GLAPPrimeCoreOf p X)) := by
  haveI := hn
  have hAX : GLAPPrimeCoreOf p X ≤ X := Subgroup.map_subtype_le (pPrimeCore p ↥X)
  have hXN : X ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).1 (gLAPPrimeCoreOf_normal p X)
  have hLN : X ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hn
  have hinfn : ((GLAPPrimeCoreOf p X ⊓ L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _
        (MulAut.conj l).injective, Subgroup.mem_normalizer_iff_map_conj_eq.1 (hXN (hLX hl)),
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLN (hLX hl))]
  have hcopX : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact coprime_card_pPrimeCore p ↥X
  have hcopinf : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L)) :=
    hcopX.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hinf : GLAPPrimeCoreOf p X ⊓ L ≤ GLAPPrimeCoreOf p L :=
    (gLAPPrimeCoreOf_eq_self_of_coprime hcopinf).symm.trans_le
      (gLAPPrimeCoreOf_le_of_normal (p := p) inf_le_right hinfn)
  have hodd_inf : Odd (Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L)) :=
    hL.of_dvd_nat (Subgroup.card_dvd_of_le hinf)
  let f : ↥(GLAPPrimeCoreOf p X) →* ↥X ⧸ (L.subgroupOf X) :=
    (QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hAX)
  have hker_eq : f.ker = (GLAPPrimeCoreOf p X ⊓ L).subgroupOf (GLAPPrimeCoreOf p X) := by
    ext a
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun ha => ⟨a.2, Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := L.subgroupOf X) _).1 ha)⟩,
      fun ha => (QuotientGroup.eq_one_iff (N := L.subgroupOf X) _).2 (Subgroup.mem_subgroupOf.2 ha.2)⟩
  have hker : Nat.card f.ker = Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hQ : Nat.card (↥X ⧸ (L.subgroupOf X)) = L.relIndex X := rfl
  have hodd_range : Odd (Nat.card f.range) :=
    hi.of_dvd_nat (hQ ▸ Subgroup.card_subgroup_dvd_card f.range)
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [← hcard, hker]
  exact hodd_inf.mul hodd_range

theorem gLAPPrimeCoreOf_eq_bot_of_relIndex_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) {L X : Subgroup G}
    (hLX : L ≤ X) (hn : (L.subgroupOf X).Normal) {k : ℕ} (hi : L.relIndex X = p ^ k)
    (hL : GLAPPrimeCoreOf p L = ⊥) : GLAPPrimeCoreOf p X = ⊥ := by
  haveI := hn
  have hAX : GLAPPrimeCoreOf p X ≤ X := Subgroup.map_subtype_le (pPrimeCore p ↥X)
  have hXN : X ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).1 (gLAPPrimeCoreOf_normal p X)
  have hLN : X ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).1 hn
  have hinfn : ((GLAPPrimeCoreOf p X ⊓ L).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _
        (MulAut.conj l).injective, Subgroup.mem_normalizer_iff_map_conj_eq.1 (hXN (hLX hl)),
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (hLN (hLX hl))]
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p X)) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact coprime_card_pPrimeCore p ↥X
  have hcopinf : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L)) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hinf : GLAPPrimeCoreOf p X ⊓ L ≤ GLAPPrimeCoreOf p L :=
    (gLAPPrimeCoreOf_eq_self_of_coprime hcopinf).symm.trans_le
      (gLAPPrimeCoreOf_le_of_normal (p := p) inf_le_right hinfn)
  rw [hL, le_bot_iff] at hinf
  let f : ↥(GLAPPrimeCoreOf p X) →* ↥X ⧸ (L.subgroupOf X) :=
    (QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hAX)
  have hker_eq : f.ker = (GLAPPrimeCoreOf p X ⊓ L).subgroupOf (GLAPPrimeCoreOf p X) := by
    ext a
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun ha => ⟨a.2, Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := L.subgroupOf X) _).1 ha)⟩,
      fun ha => (QuotientGroup.eq_one_iff (N := L.subgroupOf X) _).2 (Subgroup.mem_subgroupOf.2 ha.2)⟩
  have hker : Nat.card f.ker = Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hbot : Nat.card ↥(GLAPPrimeCoreOf p X ⊓ L) = 1 := by
    rw [hinf]
    exact Subgroup.card_bot
  have hdvd : Nat.card (GLAPPrimeCoreOf p X) ∣ p ^ k := by
    rw [← Subgroup.card_ker_mul_card_range f, hker, hbot, one_mul]
    have h1 : Nat.card f.range ∣ Nat.card (↥X ⧸ (L.subgroupOf X)) :=
      Subgroup.card_subgroup_dvd_card f.range
    rwa [show Nat.card (↥X ⧸ (L.subgroupOf X)) = L.relIndex X from rfl, hi] at h1
  have hc : Nat.Coprime (Nat.card (GLAPPrimeCoreOf p X)) (p ^ k) := hcop.symm.pow_right k
  exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hc hdvd)

theorem gLAPPrimeCore_eq_bot_of_quasisimple_of_isPGroup_center {p : ℕ} (hp : p.Prime) {Y : Type*}
    [Group Y] [Finite Y] (hq : IsQuasisimple Y) (hZ : IsPGroup p (Subgroup.center Y))
    (hdvd : p ∣ Nat.card (Y ⧸ Subgroup.center Y)) : GLAPPrimeCore p Y = ⊥ := by
  classical
  obtain ⟨-, hsimple⟩ := hq
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup Y := GLAPPrimeCore p Y with hN
  have hNn : N.Normal := inferInstance
  have hcop : Nat.Coprime p (Nat.card N) := by
    rw [hN]
    exact coprime_card_pPrimeCore p Y
  have hNZ : N ⊓ Subgroup.center Y = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ
    have h1 : Nat.card ↥(N ⊓ Subgroup.center Y) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(N ⊓ Subgroup.center Y) ∣ Nat.card ↥(Subgroup.center Y) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.Coprime (Nat.card ↥(N ⊓ Subgroup.center Y)) (p ^ k) :=
      (hcop.coprime_dvd_right h1).symm.pow_right k
    exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd h3 (hk ▸ h2))
  have hMn : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  have hker : ((QuotientGroup.mk' (Subgroup.center Y)).subgroupMap N).ker = ⊥ := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    refine le_bot_iff.1 ?_
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    have hz' : (z : Y) ∈ N ⊓ Subgroup.center Y := Subgroup.mem_inf.2 ⟨z.2, hz⟩
    rw [hNZ, Subgroup.mem_bot] at hz'
    exact Subtype.ext hz'
  have hcardM : Nat.card ↥(N.map (QuotientGroup.mk' (Subgroup.center Y))) = Nat.card N := by
    have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center Y)).subgroupMap N) :=
      (MonoidHom.ker_eq_bot_iff _).1 hker
    have hbij : Function.Bijective ((QuotientGroup.mk' (Subgroup.center Y)).subgroupMap N) :=
      ⟨hinj, (QuotientGroup.mk' (Subgroup.center Y)).subgroupMap_surjective N⟩
    exact Nat.card_congr
      (Equiv.ofBijective ((QuotientGroup.mk' (Subgroup.center Y)).subgroupMap N) hbij).symm
  haveI := hMn
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Y)))
    with h | h
  · have hNZle : N ≤ Subgroup.center Y := by
      intro n hn'
      have hmem : QuotientGroup.mk' (Subgroup.center Y) n ∈
          N.map (QuotientGroup.mk' (Subgroup.center Y)) := ⟨n, hn', rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff n).1 hmem
    have hsub : N ≤ N ⊓ Subgroup.center Y := by
      intro n hn'
      exact Subgroup.mem_inf.2 ⟨hn', hNZle hn'⟩
    rw [hNZ] at hsub
    exact le_bot_iff.1 hsub
  · exfalso
    have hdvdN : p ∣ Nat.card N := by
      rw [← hcardM, h, Subgroup.card_top]
      exact hdvd
    exact (hp.coprime_iff_not_dvd.1 hcop) hdvdN

end CFSG
